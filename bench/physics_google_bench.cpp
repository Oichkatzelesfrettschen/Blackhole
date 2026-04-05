#include <benchmark/benchmark.h>

#include <cstddef>
#include <vector>

#include "physics/xsimd_eval.h"

namespace {

constexpr double kRs = 2.0;

std::vector<double> makeLinear(std::size_t count, double start, double step) {
  std::vector<double> values(count);
  for (std::size_t i = 0; i < count; ++i) {
    values[i] = start + step * static_cast<double>(i);
  }
  return values;
}

void benchSchwarzschildScalar(benchmark::State &state) {
  std::size_t const count = static_cast<std::size_t>(state.range(0));
  std::vector<double> radii = makeLinear(count, 3.0, 0.001);
  std::vector<double> out(count, 0.0);
  for ([[maybe_unused]] auto _ : state) {
    physics::xsimd_eval::schwarzschildFScalar(radii.data(), kRs, out.data(), count);
    benchmark::DoNotOptimize(out.data());
    benchmark::ClobberMemory();
  }
  state.SetItemsProcessed(static_cast<int64_t>(state.iterations()) * static_cast<int64_t>(count));
}

void benchSchwarzschildXsimd(benchmark::State &state) {
  std::size_t const count = static_cast<std::size_t>(state.range(0));
  std::vector<double> radii = makeLinear(count, 3.0, 0.001);
  std::vector<double> out(count, 0.0);
  for ([[maybe_unused]] auto _ : state) {
    physics::xsimd_eval::schwarzschildFXsimd(radii.data(), kRs, out.data(), count);
    benchmark::DoNotOptimize(out.data());
    benchmark::ClobberMemory();
  }
  state.SetItemsProcessed(static_cast<int64_t>(state.iterations()) * static_cast<int64_t>(count));
}

void benchRedshiftScalar(benchmark::State &state) {
  std::size_t const count = static_cast<std::size_t>(state.range(0));
  std::vector<double> radii = makeLinear(count, 3.0, 0.001);
  std::vector<double> out(count, 0.0);
  for ([[maybe_unused]] auto _ : state) {
    physics::xsimd_eval::redshiftBatchScalar(radii.data(), kRs, out.data(), count);
    benchmark::DoNotOptimize(out.data());
    benchmark::ClobberMemory();
  }
  state.SetItemsProcessed(static_cast<int64_t>(state.iterations()) * static_cast<int64_t>(count));
}

void benchRedshiftXsimd(benchmark::State &state) {
  std::size_t const count = static_cast<std::size_t>(state.range(0));
  std::vector<double> radii = makeLinear(count, 3.0, 0.001);
  std::vector<double> out(count, 0.0);
  for ([[maybe_unused]] auto _ : state) {
    physics::xsimd_eval::redshiftBatchXsimd(radii.data(), kRs, out.data(), count);
    benchmark::DoNotOptimize(out.data());
    benchmark::ClobberMemory();
  }
  state.SetItemsProcessed(static_cast<int64_t>(state.iterations()) * static_cast<int64_t>(count));
}

void benchChristoffelScalar(benchmark::State &state) {
  std::size_t const count = static_cast<std::size_t>(state.range(0));
  std::vector<double> r = makeLinear(count, 4.0, 0.002);
  std::vector<double> dr(count, 0.01);
  std::vector<double> dtheta(count, 0.005);
  std::vector<double> dphi(count, 0.02);
  std::vector<double> theta(count, 1.0);
  std::vector<double> out(count, 0.0);
  for ([[maybe_unused]] auto _ : state) {
    physics::xsimd_eval::christoffelAccelScalar(
        r.data(), dr.data(), dtheta.data(), dphi.data(), theta.data(), kRs, out.data(), count);
    benchmark::DoNotOptimize(out.data());
    benchmark::ClobberMemory();
  }
  state.SetItemsProcessed(static_cast<int64_t>(state.iterations()) * static_cast<int64_t>(count));
}

void benchChristoffelXsimd(benchmark::State &state) {
  std::size_t const count = static_cast<std::size_t>(state.range(0));
  std::vector<double> r = makeLinear(count, 4.0, 0.002);
  std::vector<double> dr(count, 0.01);
  std::vector<double> dtheta(count, 0.005);
  std::vector<double> dphi(count, 0.02);
  std::vector<double> theta(count, 1.0);
  std::vector<double> out(count, 0.0);
  for ([[maybe_unused]] auto _ : state) {
    physics::xsimd_eval::christoffelAccelXsimd(
        r.data(), dr.data(), dtheta.data(), dphi.data(), theta.data(), kRs, out.data(), count);
    benchmark::DoNotOptimize(out.data());
    benchmark::ClobberMemory();
  }
  state.SetItemsProcessed(static_cast<int64_t>(state.iterations()) * static_cast<int64_t>(count));
}

} // namespace

BENCHMARK(benchSchwarzschildScalar)->RangeMultiplier(4)->Range(1 << 10, 1 << 20);
BENCHMARK(benchSchwarzschildXsimd)->RangeMultiplier(4)->Range(1 << 10, 1 << 20);
BENCHMARK(benchRedshiftScalar)->RangeMultiplier(4)->Range(1 << 10, 1 << 20);
BENCHMARK(benchRedshiftXsimd)->RangeMultiplier(4)->Range(1 << 10, 1 << 20);
BENCHMARK(benchChristoffelScalar)->RangeMultiplier(4)->Range(1 << 10, 1 << 18);
BENCHMARK(benchChristoffelXsimd)->RangeMultiplier(4)->Range(1 << 10, 1 << 18);

BENCHMARK_MAIN();
