use super::*;

fn mono(exps: &[u16]) -> Monomial {
    Monomial::from_exponents(exps.to_vec())
}

#[test]
fn basic_ops() {
    let a = mono(&[2, 1, 0]);
    let b = mono(&[1, 2, 1]);
    assert_eq!(a.total_degree(), 3);
    assert_eq!(b.total_degree(), 4);
    let prod = a.mul(&b);
    assert_eq!(prod.exponents(), &[3, 3, 1]);
    assert_eq!(prod.total_degree(), 7);
    let lcm = a.lcm(&b);
    assert_eq!(lcm.exponents(), &[2, 2, 1]);
    let gcd = a.gcd(&b);
    assert_eq!(gcd.exponents(), &[1, 1, 0]);
}

#[test]
fn divides_and_div() {
    let a = mono(&[1, 1, 0]);
    let b = mono(&[2, 1, 1]);
    assert!(a.divides(&b));
    assert!(!b.divides(&a));
    let q = b.div(&a);
    assert_eq!(q.exponents(), &[1, 0, 1]);
    assert_eq!(q.total_degree(), 2);
}

#[test]
fn coprime() {
    assert!(mono(&[1, 0, 0]).is_coprime(&mono(&[0, 2, 1])));
    assert!(!mono(&[1, 1, 0]).is_coprime(&mono(&[0, 1, 0])));
}

#[test]
fn lex_ordering() {
    // x_0^2 > x_0 x_1 (because of the first index)
    let a = mono(&[2, 0, 0]);
    let b = mono(&[1, 1, 0]);
    assert_eq!(a.cmp_with_order(&b, MonomialOrder::Lex), Ordering::Greater);
}

#[test]
fn degrevlex_ordering() {
    // Same total degree (3): x0^2 x1 vs x1^2 x2.
    // In DegRevLex, x0^2 x1 > x1^2 x2 because the rightmost-nonzero
    // exponent in x1^2 x2 is x2 (var 2, exp 1) vs x1 (var 1, exp 1) —
    // i.e. x1^2 x2 has a nonzero exponent further to the right, so it ranks LOWER.
    let a = mono(&[2, 1, 0]);
    let b = mono(&[0, 2, 1]);
    assert_eq!(a.total_degree(), b.total_degree());
    assert_eq!(
        a.cmp_with_order(&b, MonomialOrder::DegRevLex),
        Ordering::Greater
    );

    // Different degrees: x0^3 vs x0 x1
    let c = mono(&[3, 0, 0]);
    let d = mono(&[1, 1, 0]);
    assert_eq!(
        c.cmp_with_order(&d, MonomialOrder::DegRevLex),
        Ordering::Greater
    );
}
