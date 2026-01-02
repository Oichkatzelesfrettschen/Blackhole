/**
 * @file kerr_isco_calculator.cpp
 * @brief Interactive Kerr ISCO Calculator - reference implementation based on Leo Stein's tool
 *
 * Provides interactive command-line interface for computing:
 *   - Innermost Stable Circular Orbit (ISCO) radius
 *   - Photon sphere properties
 *   - Horizon dynamics
 *   - Thermodynamic parameters
 *
 * Based on:
 *   - Bardeen, Press, Teukolsky (1972) - ISCO formula
 *   - Leo Stein's Kerr Calculator (duetosymmetry.com)
 *   - Peer-reviewed research from Phase 8.3
 */

#include "../src/physics/verified/kerr.hpp"
#include <iostream>
#include <iomanip>
#include <cmath>
#include <string>
#include <vector>
#include <sstream>
#include <fstream>
#include <nlohmann/json.hpp>

using json = nlohmann::json;

/**
 * @brief Kerr black hole ISCO calculator
 *
 * Provides validated ISCO computations across full spin range [0, 1)
 */
class KerrISCOCalculator {
private:
    double M_;  // Black hole mass
    double a_;  // Spin parameter (0 <= a < M)

public:
    /**
     * @brief Initialize calculator with black hole parameters
     *
     * @param M Black hole mass (geometric units)
     * @param a Spin parameter (geometric units, 0 <= a < M)
     */
    KerrISCOCalculator(double M = 1.0, double a = 0.0)
        : M_(M), a_(std::abs(a) < M ? a : 0.9999 * M) {
        if (M <= 0.0) M_ = 1.0;
    }

    // ========================================================================
    // ISCO Calculations (Bardeen-Press-Teukolsky 1972)
    // ========================================================================

    /**
     * @brief Compute prograde ISCO radius
     *
     * @return r_isco for prograde orbits (increasing angular momentum)
     */
    [[nodiscard]] double isco_prograde() const noexcept {
        return verified::kerr_isco_prograde(M_, a_);
    }

    /**
     * @brief Compute retrograde ISCO radius
     *
     * @return r_isco for retrograde orbits (decreasing angular momentum)
     */
    [[nodiscard]] double isco_retrograde() const noexcept {
        return verified::kerr_isco_retrograde(M_, a_);
    }

    /**
     * @brief Compute average ISCO radius
     *
     * @return (r_pro + r_ret) / 2
     */
    [[nodiscard]] double isco_average() const noexcept {
        return (isco_prograde() + isco_retrograde()) / 2.0;
    }

    // ========================================================================
    // Photon Sphere Calculations
    // ========================================================================

    /**
     * @brief Compute prograde photon sphere radius
     *
     * Formula: r_ph = 2M(1 + cos(2/3 · arccos(-a*)))
     *
     * @return r_photon for prograde photons
     */
    [[nodiscard]] double photon_sphere_prograde() const noexcept {
        return verified::photon_orbit_prograde(M_, a_);
    }

    /**
     * @brief Compute retrograde photon sphere radius
     *
     * Formula: r_ph = 2M(1 + cos(2/3 · arccos(a*)))
     *
     * @return r_photon for retrograde photons
     */
    [[nodiscard]] double photon_sphere_retrograde() const noexcept {
        return verified::photon_orbit_retrograde(M_, a_);
    }

    // ========================================================================
    // Horizon Properties
    // ========================================================================

    /**
     * @brief Outer event horizon radius
     *
     * @return r_+ = M + sqrt(M² - a²)
     */
    [[nodiscard]] double outer_horizon() const noexcept {
        return verified::outer_horizon(M_, a_);
    }

    /**
     * @brief Inner event horizon radius (Cauchy horizon)
     *
     * @return r_- = M - sqrt(M² - a²)
     */
    [[nodiscard]] double inner_horizon() const noexcept {
        return verified::inner_horizon(M_, a_);
    }

    /**
     * @brief Schwarzschild limit (a → 0)
     *
     * @return 2M (both horizons collapse to r_+ = 2M, r_- = 0)
     */
    [[nodiscard]] double schwarzschild_radius() const noexcept {
        return 2.0 * M_;
    }

    // ========================================================================
    // Thermodynamic Properties
    // ========================================================================

    /**
     * @brief Surface gravity at outer horizon
     *
     * Formula: κ = (r_+ - r_-) / (2(r_+² + a²))
     *
     * @return Surface gravity [1/M]
     */
    [[nodiscard]] double surface_gravity() const noexcept {
        double r_plus = outer_horizon();
        double r_minus = inner_horizon();
        return (r_plus - r_minus) / (2.0 * (r_plus * r_plus + a_ * a_));
    }

    /**
     * @brief Hawking temperature
     *
     * Formula: T_H = κ / (8π² M)
     *
     * @return Temperature in geometric units
     */
    [[nodiscard]] double hawking_temperature() const noexcept {
        return surface_gravity() / (8.0 * M_PI_PI);
    }

    /**
     * @brief Bekenstein-Hawking entropy
     *
     * Formula: S = π(r_+² + a²)
     *
     * @return Entropy in geometric units
     */
    [[nodiscard]] double entropy() const noexcept {
        double r_plus = outer_horizon();
        return M_PI * (r_plus * r_plus + a_ * a_);
    }

    /**
     * @brief Irreducible mass
     *
     * Formula: m_irr = sqrt((r_+² + a²) / 2)
     *
     * @return Irreducible mass
     */
    [[nodiscard]] double irreducible_mass() const noexcept {
        double r_plus = outer_horizon();
        return std::sqrt((r_plus * r_plus + a_ * a_) / 2.0);
    }

    /**
     * @brief Angular momentum
     *
     * Formula: J = a × M
     *
     * @return Angular momentum
     */
    [[nodiscard]] double angular_momentum() const noexcept {
        return a_ * M_;
    }

    // ========================================================================
    // Validation & Safety Checks
    // ========================================================================

    /**
     * @brief Check if parameters are physical
     *
     * @return true if 0 <= a < M
     */
    [[nodiscard]] bool is_physical() const noexcept {
        return M_ > 0.0 && 0.0 <= a_ && a_ < M_;
    }

    /**
     * @brief Check if black hole is extremal
     *
     * @return true if a ≈ M (within numerical precision)
     */
    [[nodiscard]] bool is_extremal(double tolerance = 1e-6) const noexcept {
        return std::abs(a_ - M_) < tolerance;
    }

    /**
     * @brief Spin parameter (normalized to [0,1])
     *
     * @return a / M
     */
    [[nodiscard]] double spin_parameter() const noexcept {
        return a_ / M_;
    }

    // ========================================================================
    // Constants
    // ========================================================================

    static constexpr double M_PI_PI = 9.8696044010893586188344909998762;  // π²

    // ========================================================================
    // Accessors
    // ========================================================================

    [[nodiscard]] double mass() const noexcept { return M_; }
    [[nodiscard]] double spin() const noexcept { return a_; }

    void set_mass(double M) noexcept { M_ = std::max(M, 0.001); }
    void set_spin(double a) noexcept { a_ = std::min(std::abs(a), 0.9999 * M_); }
};

// ============================================================================
// Interactive CLI and Export Functions
// ============================================================================

/**
 * @brief Print formatted header
 */
void print_header() {
    std::cout << "\n============================================================\n"
              << "   Kerr Black Hole ISCO Calculator (Phase 8.5)\n"
              << "   Based on Bardeen-Press-Teukolsky and Leo Stein's tool\n"
              << "============================================================\n\n";
}

/**
 * @brief Print summary of black hole parameters
 */
void print_summary(const KerrISCOCalculator& calc) {
    std::cout << std::fixed << std::setprecision(6);

    std::cout << "===========================================================\n"
              << "BLACK HOLE PARAMETERS\n"
              << "===========================================================\n";

    std::cout << "Mass (M)                  : " << calc.mass() << " M☉\n"
              << "Spin Parameter (a)       : " << calc.spin() << " M\n"
              << "Spin Parameter (a/M)     : " << calc.spin_parameter() << "\n"
              << "Physical                 : " << (calc.is_physical() ? "Yes" : "No") << "\n"
              << "Extremal (a=M)           : " << (calc.is_extremal() ? "Yes" : "No") << "\n\n";

    std::cout << "===========================================================\n"
              << "HORIZONS & CIRCULAR ORBITS\n"
              << "===========================================================\n";

    std::cout << "Outer Horizon (r₊)       : " << calc.outer_horizon() << " M\n"
              << "Inner Horizon (r₋)       : " << calc.inner_horizon() << " M\n"
              << "\n"
              << "Prograde ISCO            : " << calc.isco_prograde() << " M\n"
              << "Retrograde ISCO          : " << calc.isco_retrograde() << " M\n"
              << "Average ISCO             : " << calc.isco_average() << " M\n"
              << "\n"
              << "Prograde Photon Sphere   : " << calc.photon_sphere_prograde() << " M\n"
              << "Retrograde Photon Sphere : " << calc.photon_sphere_retrograde() << " M\n\n";

    std::cout << "===========================================================\n"
              << "THERMODYNAMIC PROPERTIES\n"
              << "===========================================================\n";

    std::cout << "Surface Gravity (κ)      : " << calc.surface_gravity() << " M⁻¹\n"
              << "Hawking Temperature      : " << calc.hawking_temperature() << " M⁻¹\n"
              << "Bekenstein-Hawking Entropy: " << calc.entropy() << "\n"
              << "Irreducible Mass         : " << calc.irreducible_mass() << " M\n"
              << "Angular Momentum (J)     : " << calc.angular_momentum() << " M²\n\n";
}

/**
 * @brief Export results to JSON format
 */
json export_to_json(const KerrISCOCalculator& calc) {
    json result;

    result["parameters"]["mass"] = calc.mass();
    result["parameters"]["spin"] = calc.spin();
    result["parameters"]["spin_parameter"] = calc.spin_parameter();
    result["parameters"]["is_physical"] = calc.is_physical();
    result["parameters"]["is_extremal"] = calc.is_extremal();

    result["horizons"]["outer"] = calc.outer_horizon();
    result["horizons"]["inner"] = calc.inner_horizon();

    result["isco"]["prograde"] = calc.isco_prograde();
    result["isco"]["retrograde"] = calc.isco_retrograde();
    result["isco"]["average"] = calc.isco_average();

    result["photon_sphere"]["prograde"] = calc.photon_sphere_prograde();
    result["photon_sphere"]["retrograde"] = calc.photon_sphere_retrograde();

    result["thermodynamics"]["surface_gravity"] = calc.surface_gravity();
    result["thermodynamics"]["hawking_temperature"] = calc.hawking_temperature();
    result["thermodynamics"]["entropy"] = calc.entropy();
    result["thermodynamics"]["irreducible_mass"] = calc.irreducible_mass();
    result["thermodynamics"]["angular_momentum"] = calc.angular_momentum();

    return result;
}

/**
 * @brief Interactive calculator session
 */
int main() {
    print_header();

    double M = 1.0;
    double a = 0.5;

    // Check command line arguments for batch mode
    std::vector<std::string> spins = {"0.0", "0.3", "0.5", "0.7", "0.9", "0.98"};

    std::cout << "Computing ISCO values for reference spins...\n\n";
    std::cout << std::left << std::setw(10) << "Spin (a/M)"
              << std::setw(15) << "r_isco (pro)"
              << std::setw(15) << "r_isco (ret)"
              << std::setw(15) << "Δr (ret-pro)\n";
    std::cout << std::string(55, '-') << "\n";

    json batch_results = json::array();

    for (const auto& spin_str : spins) {
        double spin_param = std::stod(spin_str);
        KerrISCOCalculator calc(1.0, spin_param);

        double r_pro = calc.isco_prograde();
        double r_ret = calc.isco_retrograde();
        double delta = r_ret - r_pro;

        std::cout << std::fixed << std::setprecision(3)
                  << std::left << std::setw(10) << spin_param
                  << std::setw(15) << r_pro
                  << std::setw(15) << r_ret
                  << std::setw(15) << delta << "\n";

        batch_results.push_back(export_to_json(calc));
    }

    // Interactive section
    std::cout << "\n" << std::string(60, '=') << "\n";
    std::cout << "INTERACTIVE MODE\n"
              << "Commands: calc [M] [a] | export | quit\n"
              << std::string(60, '=') << "\n\n";

    std::string line;
    KerrISCOCalculator calc(M, a);

    while (std::getline(std::cin, line)) {
        if (line.empty()) continue;

        std::istringstream iss(line);
        std::string command;
        iss >> command;

        if (command == "quit" || command == "q") {
            break;
        } else if (command == "calc") {
            double M_input, a_input;
            if (iss >> M_input >> a_input) {
                calc.set_mass(M_input);
                calc.set_spin(a_input);
                print_summary(calc);
            } else {
                std::cout << "Usage: calc <M> <a>\n";
            }
        } else if (command == "export") {
            json result = export_to_json(calc);
            std::string filename = "isco_calculation.json";
            std::ofstream file(filename);
            file << result.dump(2);
            file.close();
            std::cout << "Exported to " << filename << "\n";
        } else {
            std::cout << "Unknown command. Try: calc, export, or quit\n";
        }
    }

    std::cout << "\nThank you for using the Kerr ISCO Calculator!\n";
    return 0;
}
