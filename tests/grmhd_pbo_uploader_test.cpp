/**
 * @file grmhd_pbo_uploader_test.cpp
 * @brief Headless validation of GrmhdPBOUploader state machine and logic.
 *
 * WHY: GrmhdPBOUploader contains GL calls that require an OpenGL context, so
 *      the full upload path cannot be tested headlessly.  However, the state
 *      machine (initialization guards, size validation, index rotation, ready
 *      flag) and the surrounding logic (double-buffer cycle, orphan pattern)
 *      can be verified by mocking out the GL layer.
 *
 * WHAT: Each test exercises one invariant of the uploader:
 *   1. Uploader starts in a clean state (texture=0, not ready, size=0).
 *   2. init() with invalid dimensions returns false and leaves state clean.
 *   3. upload() before init() returns false without crashing.
 *   4. upload() with wrong nFloats returns false (size guard).
 *   5. PBO dimensions encode nFloats correctly (w*h*d*4).
 *   6. First-upload prime path vs. steady-state path are distinguished by
 *      uploadCount_ (observable via ready()).
 *   7. shutdown() resets all state back to zero.
 *   8. Re-init after shutdown() succeeds (lifecycle round-trip).
 *   9. Double init() without shutdown is rejected (no double alloc).
 *  10. Orphan count per upload matches expected pattern.
 *
 * HOW: MockPBOUploader replicates the GrmhdPBOUploader state machine exactly
 *      but replaces GL calls with counters.  All mock_gl counters and the
 *      MockPBOUploader class live in the anonymous namespace to satisfy
 *      misc-use-anonymous-namespace and misc-use-internal-linkage.
 *
 * Note: The actual glTexSubImage3D / glMapBuffer / glUnmapBuffer calls are
 *       validated end-to-end by z3_verification and grmhd_pack_fixture tests
 *       which run with an OpenGL window.
 */

#include <cstddef>
#include <cstring>
#include <iostream>
#include <utility>
#include <vector>

namespace {

/* =========================================================================
 * Mock GL counters (replace glXxx calls; all internal to this TU)
 * ======================================================================= */

int gTexSubImageDirectCalls = 0; // "prime" path (no PBO bound)
int gTexSubImagePBOCalls    = 0; // PBO DMA path (nullptr offset)
int gMapBufferCalls         = 0;
int gUnmapBufferCalls       = 0;
int gOrphanCalls            = 0; // glBufferData(..., nullptr) re-allocs
int gGenTexturesCalls       = 0;
int gGenBuffersCalls        = 0;
int gDeleteTexturesCalls    = 0;
int gDeleteBuffersCalls     = 0;

void resetCounters() {
  gTexSubImageDirectCalls = 0;
  gTexSubImagePBOCalls    = 0;
  gMapBufferCalls         = 0;
  gUnmapBufferCalls       = 0;
  gOrphanCalls            = 0;
  gGenTexturesCalls       = 0;
  gGenBuffersCalls        = 0;
  gDeleteTexturesCalls    = 0;
  gDeleteBuffersCalls     = 0;
}

/* =========================================================================
 * MockPBOUploader: mirrors GrmhdPBOUploader, GL calls replaced by counters
 * ======================================================================= */

class MockPBOUploader {
public:
  MockPBOUploader() = default;
  ~MockPBOUploader() { shutdown(); }

  MockPBOUploader(const MockPBOUploader &) = delete;
  MockPBOUploader &operator=(const MockPBOUploader &) = delete;

  bool init(int width, int height, int depth) {
    if (texture_ != 0)                    { return false; }
    if (width <= 0 || height <= 0 || depth <= 0) { return false; }

    width_   = width;
    height_  = height;
    depth_   = depth;
    nFloats_ = static_cast<std::size_t>(width) *
               static_cast<std::size_t>(height) *
               static_cast<std::size_t>(depth) * 4u;

    texture_  = 1u;
    pbos_[0]  = 2u;
    pbos_[1]  = 3u;
    gGenTexturesCalls++;
    gGenBuffersCalls++;
    return true;
  }

  bool upload(const float *data, std::size_t nFloats) {
    if (texture_ == 0 || data == nullptr) { return false; }
    if (nFloats != nFloats_)              { return false; }

    if (uploadCount_ == 0) {
      gTexSubImageDirectCalls++;
      gOrphanCalls++;
      gMapBufferCalls++;
      stagingBuf_.assign(data, data + nFloats);
      gUnmapBufferCalls++;
      std::swap(writeIdx_, readIdx_);
      ++uploadCount_;
      return true;
    }

    gOrphanCalls++;
    gMapBufferCalls++;
    stagingBuf_.assign(data, data + nFloats);
    gUnmapBufferCalls++;
    gTexSubImagePBOCalls++;
    std::swap(writeIdx_, readIdx_);
    ++uploadCount_;
    return true;
  }

  [[nodiscard]] unsigned fakeTexture() const noexcept { return texture_; }
  [[nodiscard]] bool     ready()       const noexcept { return uploadCount_ > 0; }
  [[nodiscard]] int      width()       const noexcept { return width_; }
  [[nodiscard]] int      height()      const noexcept { return height_; }
  [[nodiscard]] int      depth()       const noexcept { return depth_; }
  [[nodiscard]] unsigned uploadCount() const noexcept { return uploadCount_; }
  [[nodiscard]] int      writeIdx()    const noexcept { return writeIdx_; }
  [[nodiscard]] int      readIdx()     const noexcept { return readIdx_; }

  void shutdown() {
    if (pbos_[0] != 0 || pbos_[1] != 0) {
      gDeleteBuffersCalls++;
      pbos_[0] = 0;
      pbos_[1] = 0;
    }
    if (texture_ != 0) {
      gDeleteTexturesCalls++;
      texture_ = 0;
    }
    width_       = 0;
    height_      = 0;
    depth_       = 0;
    nFloats_     = 0;
    writeIdx_    = 0;
    readIdx_     = 1;
    uploadCount_ = 0;
    stagingBuf_.clear();
  }

private:
  unsigned    texture_{0};
  unsigned    pbos_[2]{0, 0};
  int         width_{0};
  int         height_{0};
  int         depth_{0};
  std::size_t nFloats_{0};
  int         writeIdx_{0};
  int         readIdx_{1};
  unsigned    uploadCount_{0};
  std::vector<float> stagingBuf_;
};

/* =========================================================================
 * Test helpers
 * ======================================================================= */

bool gAllPass = true;

void check(bool cond, const char *name, const char *detail = "") {
  if (cond) {
    std::cout << "  [PASS] " << name << "\n";
  } else {
    std::cout << "  [FAIL] " << name;
    if (detail[0] != '\0') { std::cout << " -- " << detail; }
    std::cout << "\n";
    gAllPass = false;
  }
}

std::vector<float> makeData(int w, int h, int d) {
  return std::vector<float>(static_cast<std::size_t>(w) *
                            static_cast<std::size_t>(h) *
                            static_cast<std::size_t>(d) * 4u, 1.0f);
}

/* =========================================================================
 * Test 1: clean initial state
 * ======================================================================= */
void testInitialState() {
  std::cout << "Test 1: initial state is clean\n";
  const MockPBOUploader up;
  check(up.fakeTexture() == 0, "texture_ == 0 before init");
  check(!up.ready(),           "ready() == false before init");
  check(up.width()  == 0,      "width == 0 before init");
  check(up.height() == 0,      "height == 0 before init");
  check(up.depth()  == 0,      "depth == 0 before init");
}

/* =========================================================================
 * Test 2: invalid dimensions rejected
 * ======================================================================= */
void testInvalidDimensions() {
  std::cout << "Test 2: invalid dimensions rejected\n";
  MockPBOUploader up;
  check(!up.init(0,  16, 16), "init(0,16,16) returns false");
  check(!up.init(16,  0, 16), "init(16,0,16) returns false");
  check(!up.init(16, 16,  0), "init(16,16,0) returns false");
  check(!up.init(-1, 16, 16), "init(-1,16,16) returns false");
  check(up.fakeTexture() == 0, "texture_ still 0 after failed inits");
}

/* =========================================================================
 * Test 3: upload before init returns false
 * ======================================================================= */
void testUploadBeforeInit() {
  std::cout << "Test 3: upload() before init() returns false\n";
  MockPBOUploader up;
  const std::vector<float> data(64, 0.0f);
  check(!up.upload(data.data(), data.size()),
        "upload() before init() returns false");
  check(!up.ready(), "ready() still false after failed upload");
}

/* =========================================================================
 * Test 4: size guard rejects wrong nFloats
 * ======================================================================= */
void testSizeGuard() {
  std::cout << "Test 4: upload() rejects wrong nFloats\n";
  MockPBOUploader up;
  up.init(8, 8, 8); // nFloats_ = 8*8*8*4 = 2048
  const std::vector<float> wrong(100, 0.0f);
  check(!up.upload(wrong.data(), wrong.size()),
        "upload with wrong size returns false");
  check(!up.ready(), "ready() false after rejected upload");
}

/* =========================================================================
 * Test 5: nFloats encoding (w*h*d*4)
 * ======================================================================= */
void testNFloatsEncoding() {
  std::cout << "Test 5: nFloats_ = w*h*d*4\n";
  struct Case {
    int w, h, d;
    std::size_t expected;
  };
  const Case cases[] = {
    {.w= 8, .h= 8, .d= 8, .expected=std::size_t{ 8}*  8*  8*4},
    {.w=16, .h=16, .d=16, .expected=std::size_t{16}* 16* 16*4},
    {.w=32, .h=32, .d=16, .expected=std::size_t{32}* 32* 16*4},
    {.w=64, .h=64, .d=64, .expected=std::size_t{64}* 64* 64*4},
  };
  for (const auto &c : cases) {
    MockPBOUploader up;
    up.init(c.w, c.h, c.d);
    const auto data = makeData(c.w, c.h, c.d);
    check(data.size() == c.expected, "data.size() matches w*h*d*4");
    const bool ok = up.upload(data.data(), data.size());
    check(ok,         "upload succeeds with correct nFloats");
    check(up.ready(), "ready() true after upload");
  }
}

/* =========================================================================
 * Test 6: first upload uses prime path, second uses PBO path
 * ======================================================================= */
void testPrimeVsPBODispatch() {
  std::cout << "Test 6: first upload primes directly; second uses PBO\n";
  resetCounters();

  MockPBOUploader up;
  up.init(8, 8, 8);
  const auto data = makeData(8, 8, 8);

  up.upload(data.data(), data.size());
  check(gTexSubImageDirectCalls == 1, "prime path: 1 direct glTexSubImage3D");
  check(gTexSubImagePBOCalls    == 0, "prime path: 0 PBO glTexSubImage3D");
  check(up.uploadCount() == 1,        "uploadCount_ == 1 after first upload");

  up.upload(data.data(), data.size());
  check(gTexSubImageDirectCalls == 1, "PBO path: still 1 direct call total");
  check(gTexSubImagePBOCalls    == 1, "PBO path: 1 PBO call");
  check(up.uploadCount() == 2,        "uploadCount_ == 2 after second upload");

  up.upload(data.data(), data.size());
  check(gTexSubImagePBOCalls == 2,    "PBO path: 2 PBO calls total");
}

/* =========================================================================
 * Test 7: index rotation (write/read swap each call)
 * ======================================================================= */
void testIndexRotation() {
  std::cout << "Test 7: write/read index rotates each upload call\n";
  MockPBOUploader up;
  up.init(4, 4, 4);
  const auto data = makeData(4, 4, 4);

  check(up.writeIdx() == 0 && up.readIdx() == 1,
        "initial: writeIdx=0, readIdx=1");

  up.upload(data.data(), data.size());
  check(up.writeIdx() == 1 && up.readIdx() == 0,
        "after call 1: writeIdx=1, readIdx=0");

  up.upload(data.data(), data.size());
  check(up.writeIdx() == 0 && up.readIdx() == 1,
        "after call 2: writeIdx=0, readIdx=1 (restored)");
}

/* =========================================================================
 * Test 8: shutdown resets all state; re-init succeeds
 * ======================================================================= */
void testShutdownAndReinit() {
  std::cout << "Test 8: shutdown resets state; re-init succeeds\n";
  resetCounters();

  MockPBOUploader up;
  up.init(8, 8, 8);
  const auto data = makeData(8, 8, 8);
  up.upload(data.data(), data.size());
  up.upload(data.data(), data.size());

  check(up.ready(), "ready() true before shutdown");
  up.shutdown();

  check(!up.ready(),            "ready() false after shutdown");
  check(up.fakeTexture() == 0,  "texture_ 0 after shutdown");
  check(up.width()  == 0,       "width 0 after shutdown");
  check(up.height() == 0,       "height 0 after shutdown");
  check(up.depth()  == 0,       "depth 0 after shutdown");
  check(up.writeIdx() == 0,     "writeIdx reset to 0");
  check(up.readIdx()  == 1,     "readIdx reset to 1");
  check(gDeleteTexturesCalls == 1, "deleteTextures called once");
  check(gDeleteBuffersCalls  == 1, "deleteBuffers called once");

  const bool reinitOk = up.init(16, 16, 8);
  check(reinitOk,           "init() succeeds after shutdown");
  check(up.width()  == 16,  "width == 16 after re-init");
  check(up.height() == 16,  "height == 16 after re-init");
  check(up.depth()  ==  8,  "depth == 8 after re-init");
}

/* =========================================================================
 * Test 9: double init() without shutdown is rejected
 * ======================================================================= */
void testDoubleInitRejected() {
  std::cout << "Test 9: double init() without shutdown is rejected\n";
  MockPBOUploader up;
  const bool first  = up.init(8, 8, 8);
  const bool second = up.init(8, 8, 8);
  check(first,   "first init() returns true");
  check(!second, "second init() without shutdown returns false");
}

/* =========================================================================
 * Test 10: orphan count matches expected pattern (1 per upload call)
 * ======================================================================= */
void testOrphanPattern() {
  std::cout << "Test 10: orphan count is 1 per upload call\n";
  resetCounters();

  MockPBOUploader up;
  up.init(8, 8, 8);
  const auto data = makeData(8, 8, 8);

  up.upload(data.data(), data.size());
  check(gOrphanCalls == 1, "after call 1: 1 orphan");

  up.upload(data.data(), data.size());
  check(gOrphanCalls == 2, "after call 2: 2 orphans");

  up.upload(data.data(), data.size());
  check(gOrphanCalls == 3, "after call 3: 3 orphans");
}

} // namespace

int main() {
  std::cout << "\n================================================\n"
            << "GRMHD PBO UPLOADER STATE MACHINE VALIDATION\n"
            << "Headless mock; GL calls replaced with counters\n"
            << "================================================\n\n";

  testInitialState();       std::cout << "\n";
  testInvalidDimensions();  std::cout << "\n";
  testUploadBeforeInit();   std::cout << "\n";
  testSizeGuard();          std::cout << "\n";
  testNFloatsEncoding();    std::cout << "\n";
  testPrimeVsPBODispatch(); std::cout << "\n";
  testIndexRotation();      std::cout << "\n";
  testShutdownAndReinit();  std::cout << "\n";
  testDoubleInitRejected(); std::cout << "\n";
  testOrphanPattern();      std::cout << "\n";

  std::cout << "================================================\n"
            << "RESULT: " << (gAllPass ? "ALL PASS" : "FAILURES DETECTED") << "\n"
            << "================================================\n\n";

  return gAllPass ? 0 : 1;
}
