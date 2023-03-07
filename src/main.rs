use ark_ff::{Field, /* FftField */ };
use ark_poly::{
    Polynomial,
    univariate::DensePolynomial, 
    EvaluationDomain, 
    Radix2EvaluationDomain,
    Evaluations
};
use ark_std::{UniformRand, test_rng, ops::*};

type F = ark_bls12_381::Fr;

fn main() {
    // set n to the desired positive integer
    // let n: u64 = 8;

    // // create an evaluation domain of size n
    // let domain: Radix2EvaluationDomain<F> = Radix2EvaluationDomain::<F>::new(8).unwrap();
    // let mut evals = vec![];
    // for i in 0..n {
    //     evals.push(F::from(i));
    // }
    // let eval_form = Evaluations::from_vec_and_domain(evals, domain);
    // let poly: DensePolynomial<F> = eval_form.interpolate();
    // println!("degree of poly: {:?}", poly.degree());
    // println!("poly coeff: {}", poly.coeffs[0]);
    

    // let group_gen = F::get_root_of_unity(n).unwrap();
    // println!("The nth root of unity is: {:?}", group_gen);
    // let omega_squared = group_gen.pow([n]);
    // println!("The omega_squared of unity is: {:?}", omega_squared);
    // // Check that it is indeed the 2^(log_size_of_group) root of unity.
    // //debug_assert_eq!(group_gen.pow([size]), F::one());
    

    // compute the nth root of unity
    let n: u64 = 8;
    let domain = Radix2EvaluationDomain::<F>::new(8).unwrap();
    let ω: F = domain.group_gen;
    //println!("The nth root of unity is: {:?}", ω);
    //println!("The omega_n_minus_1 of unity is: {:?}", ω.pow([n-1]));
    //println!("The omega_n of unity is: {:?}", ω_pow_n_minus_1 * ω);

    let weights: Vec<u64> = vec![2, 3, 4, 5, 4, 3, 2];
    let bitmap: Vec<u64> = vec![1, 1, 0, 1, 0, 1, 1];

    let w_of_x = compute_w_poly(&weights, &bitmap);
    let w_of_ωx = poly_domain_mult_ω(&w_of_x, &ω);

    let b_of_x = compute_b_poly(&bitmap);
    let b_of_ωx = poly_domain_mult_ω(&b_of_x, &ω);

    let psw_of_x = compute_psw_poly(&weights, &bitmap);
    let psw_of_ωx = poly_domain_mult_ω(&psw_of_x, &ω);

    //t(X) = ParSumW(ω · X) − ParSumW(X) − W(ω · X) · b(ω · X)
    let t_of_x = psw_of_ωx.sub(&psw_of_x).sub(&w_of_ωx.mul(&b_of_ωx));
    let z_of_x = compute_vanishing_poly(n); //returns Z(X) = X^n - 1
    let q_of_x = t_of_x.div(&z_of_x);
    
    test_poly_domain_mult(&w_of_x, &w_of_ωx, &ω);
    test_poly_domain_mult(&b_of_x, &b_of_ωx, &ω);
    test_poly_domain_mult(&psw_of_x, &psw_of_ωx, &ω);

    sanity_test_psw(&w_of_x, &b_of_x, &psw_of_x, &q_of_x);

}

fn test_poly_domain_mult(f_of_x: &DensePolynomial<F>, f_of_ωx: &DensePolynomial<F>, ω: &F) {
    let mut rng = test_rng();
    let r = F::rand(&mut rng);
    let ωr: F = ω.clone() * r;

    println!("f(x) at ωr = {:?}", f_of_x.evaluate(&ωr));
    println!("f(ωx) at r = {:?}", f_of_ωx.evaluate(&r));
    assert_eq!(f_of_x.evaluate(&ωr), f_of_ωx.evaluate(&r));
}

//returns t(X) = X^n - 1
fn compute_vanishing_poly(n: u64) -> DensePolynomial<F> {
    let mut coeffs = vec![];
    for i in 0..n+1 {
        if i == 0 {
            coeffs.push(F::from(0) - F::from(1)); // -1
        } else if i == n {
            coeffs.push(F::from(1)); // X^n
        } else {
            coeffs.push(F::from(0));
        }
    }
    DensePolynomial { coeffs }
}

fn poly_domain_mult_ω(f: &DensePolynomial<F>, ω: &F) -> DensePolynomial<F> {
    let mut new_poly = f.clone();
    for i in 1..(f.degree() + 1) { //we don't touch the zeroth coefficient
        let ω_pow_i: F = ω.pow([i as u64]);
        new_poly.coeffs[i] = new_poly.coeffs[i] * ω_pow_i;
    }
    new_poly
}

fn sanity_test_psw(
    w_of_x: &DensePolynomial<F>,
    b_of_x: &DensePolynomial<F>,
    psw_of_x: &DensePolynomial<F>,
    q_of_x: &DensePolynomial<F>
) {

    let mut rng = test_rng();
    let r = F::rand(&mut rng);

    let n: u64 = (b_of_x.degree() + 1) as u64;
    println!("n = {:?}", n);
    let domain = Radix2EvaluationDomain::<F>::new(8).unwrap();
    let ω: F = domain.group_gen;
    let ω_pow_n_minus_1: F = ω.pow([n-1]);
    let ωr: F = ω * r;

    println!("---------- sanity test ----------");

    let psw_of_r = psw_of_x.evaluate(&r);
    let psw_of_ωr = psw_of_x.evaluate(&ωr);
    let w_of_ωr = w_of_x.evaluate(&ωr);
    let b_of_ωr = b_of_x.evaluate(&ωr);
    let q_of_r = q_of_x.evaluate(&r);
    let vanishing_of_r: F = r.pow([n]) - F::from(1);

    //ParSumW(ωr) − ParSumW(r) − W(ωr) · b(ωr) = Q2(r) · (r^n − 1)
    let tmp1 = psw_of_ωr - psw_of_r - w_of_ωr * b_of_ωr;
    let tmp2 = q_of_r * vanishing_of_r;
    println!("ParSumW(ωr) - ParSumW(r) - W(ωr)·b(ωr) = {:?}", tmp1);
    println!("Q(r) · (r^n - 1) = {:?}", tmp2);
    assert_eq!(tmp1, tmp2);

    //ParSumW(ωn−1) = 0
    let psw_of_ω_pow_n_minus_1 = psw_of_x.evaluate(&ω_pow_n_minus_1);
    println!("ParSumW(ω^(n-1)) = {:?}", psw_of_ω_pow_n_minus_1);
}

fn compute_w_poly(weights: &Vec<u64>, bitmap: &Vec<u64>) -> DensePolynomial<F> {
    let num_parties = weights.len();
    //we need n = #parties + 1, for nth root of unity
    let n = num_parties + 1;
    
    let mut evals = vec![];
    let mut total_weight = 0;
    for i in 0..num_parties {
        evals.push(F::from(weights[i]));
        total_weight += if bitmap[i] == 1 { weights[i] } else { 0 };
    }
    //last entry is the additive inverse of cumulative weight
    evals.push(F::from(0) - F::from(total_weight));

    let domain = Radix2EvaluationDomain::<F>::new(n).unwrap();
    let eval_form = Evaluations::from_vec_and_domain(evals, domain);
    eval_form.interpolate()
}

fn compute_b_poly(bitmap: &Vec<u64>) -> DensePolynomial<F> {
    let num_parties = bitmap.len();
    //we need n = #parties + 1, for nth root of unity
    let n = num_parties + 1;

    let mut evals = vec![];
    for i in 0..num_parties {
        evals.push(F::from(bitmap[i]));
    }
    //last entry is 1 to activate the additive inverse of total weight
    evals.push(F::from(1));

    let domain = Radix2EvaluationDomain::<F>::new(n).unwrap();
    let eval_form = Evaluations::from_vec_and_domain(evals, domain);
    eval_form.interpolate()
}

fn compute_psw_poly(weights: &Vec<u64>, bitmap: &Vec<u64>) -> DensePolynomial<F> {
    let num_parties = bitmap.len();
    //we need n = #parties + 1, for nth root of unity
    let n = num_parties + 1;

    let mut parsum = 0;
    let mut evals = vec![];
    for i in 0..num_parties {
        let w_i_b_i = if bitmap[i] == 1 { weights[i] } else { 0 };
        parsum += w_i_b_i;
        evals.push(F::from(parsum));
    }
    //last entry is 1 to activate the additive inverse of total weight
    evals.push(F::from(0));

    let domain = Radix2EvaluationDomain::<F>::new(n).unwrap();
    let eval_form = Evaluations::from_vec_and_domain(evals, domain);
    eval_form.interpolate()    
}

// 1 at omega^i and 0 elsewhere on domain {omega^i}_{i \in [n]}
fn _lagrange_poly(n: usize, i: usize) -> DensePolynomial<F> {
    //todo: check n is a power of 2
    let mut evals = vec![];
    for j in 0..n {
        let l_of_x: u64 = if i == j { 1 } else { 0 };
        evals.push(F::from(l_of_x));
    }

    //powers of nth root of unity
    let domain = Radix2EvaluationDomain::<F>::new(n).unwrap();
    let eval_form = 
        Evaluations::from_vec_and_domain(evals, domain);
    //interpolated polynomial over the n points
    eval_form.interpolate()
}
