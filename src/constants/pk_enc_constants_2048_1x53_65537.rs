/// `N` is the degree of the cyclotomic polynomial defining the ring `Rq = Zq[X]/(X^N + 1)`.
pub const N: usize = 2048;
/// The coefficients of the polynomial `u` should exist in the interval `[-U_BOUND, U_BOUND]`.
pub const U_BOUND: u64 = 1;
/// The coefficients of the polynomial `e0` should exist in the interval `[-E0_BOUND, E0_BOUND]`.
pub const E0_BOUND: u64 = 19;
/// The coefficients of the polynomial `e1` should exist in the interval `[-E1_BOUND, E1_BOUND]`.
pub const E1_BOUND: u64 = 19;
/// The coefficients of `k1` should exist in the interval `[-K1_BOUND, K1_BOUND]`.
pub const K1_BOUND: u64 = 32768;
pub const R1_BOUNDS: [u64; 1] = [20368];
pub const R2_BOUNDS: [u64; 1] = [3471589854547519];
pub const P1_BOUNDS: [u64; 1] = [1024];
pub const P2_BOUNDS: [u64; 1] = [3471589854547519];
pub const QIS: [&str; 1] = ["6943179709095039"];
pub const K0IS: [&str; 1] = ["4098612896619616"];
