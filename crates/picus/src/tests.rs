use super::*;

#[test]
fn split_model_filters_aux_and_routes_copies() {
    let mut model = HashMap::new();
    model.insert("x0".to_string(), BigUint::from(1u32)); // input (no y0): shared
    model.insert("x5".to_string(), BigUint::from(7u32)); // orig copy (has y5)
    model.insert("y5".to_string(), BigUint::from(9u32)); // alt copy
    model.insert("__w_diseq_0".to_string(), BigUint::from(3u32)); // aux: filtered
    model.insert("__bitsum_0".to_string(), BigUint::from(4u32)); // aux: filtered
    model.insert("one".to_string(), BigUint::from(1u32)); // named constant: filtered

    let (w1, w2) = split_model(&model);

    // witness 1: original copies only, no aux / constants.
    assert_eq!(w1.get("x0"), Some(&BigUint::from(1u32)));
    assert_eq!(w1.get("x5"), Some(&BigUint::from(7u32)));
    assert!(!w1.contains_key("__w_diseq_0"));
    assert!(!w1.contains_key("__bitsum_0"));
    assert!(!w1.contains_key("one"));

    // witness 2: alt copy y5, input x0 echoed (shared), no aux.
    assert_eq!(w2.get("y5"), Some(&BigUint::from(9u32)));
    assert_eq!(w2.get("x0"), Some(&BigUint::from(1u32)));
    assert!(!w2.contains_key("__w_diseq_0"));
    assert!(!w2.contains_key("__bitsum_0"));
}
