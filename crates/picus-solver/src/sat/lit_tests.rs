use super::*;

#[test]
fn lit_polarity_roundtrip() {
    let v = Var(7);
    let p = Lit::pos(v);
    let n = Lit::neg(v);
    assert_eq!(p.var(), v);
    assert_eq!(n.var(), v);
    assert!(p.is_positive());
    assert!(!n.is_positive());
    assert!(n.is_negative());
    assert_eq!(-p, n);
    assert_eq!(-n, p);
    assert_eq!(-(-p), p);
}

#[test]
fn lit_index_disjoint_for_polarities() {
    let v = Var(3);
    let p = Lit::pos(v);
    let n = Lit::neg(v);
    assert_ne!(p.index(), n.index());
    assert_eq!(p.index(), 2 * v.index());
    assert_eq!(n.index(), 2 * v.index() + 1);
}

#[test]
fn lbool_negation() {
    assert_eq!(LBool::True.negate(), LBool::False);
    assert_eq!(LBool::False.negate(), LBool::True);
    assert_eq!(LBool::Undef.negate(), LBool::Undef);
}

#[test]
fn lbool_from_bool() {
    assert!(LBool::from_bool(true).is_true());
    assert!(LBool::from_bool(false).is_false());
}

#[test]
fn lit_raw_roundtrip() {
    let v = Var(42);
    let p = Lit::pos(v);
    let n = Lit::neg(v);
    assert_eq!(Lit::from_raw(p.raw()), p);
    assert_eq!(Lit::from_raw(n.raw()), n);
}

#[test]
fn lbool_is_defined() {
    assert!(LBool::True.is_defined());
    assert!(LBool::False.is_defined());
    assert!(!LBool::Undef.is_defined());
}

#[test]
fn lit_display_positive_and_negative() {
    let v = Var(5);
    assert_eq!(format!("{}", Lit::pos(v)), "x5");
    assert_eq!(format!("{}", Lit::neg(v)), "-x5");
}

#[test]
fn lit_display_var_zero() {
    let v = Var(0);
    assert_eq!(format!("{}", Lit::pos(v)), "x0");
    assert_eq!(format!("{}", Lit::neg(v)), "-x0");
}
