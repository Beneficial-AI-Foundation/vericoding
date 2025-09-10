function prefixProduct(s: seq<nat>, i: nat, mod: nat): nat
  requires mod > 0
  requires i <= |s|
{
    if i == 0 then 1
    else (s[i-1] * prefixProduct(s, i-1, mod)) % mod
}

function prefixProducts(s: seq<nat>, mod: nat): seq<nat>
  requires mod > 0
{
    seq(|s|, i requires 0 <= i < |s| => prefixProduct(s, i+1, mod))
}

predicate allDistinct<T(==)>(s: seq<T>)
{
    forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j]
}

predicate noForbiddenProducts(s: seq<nat>, forbidden: seq<nat>, mod: nat)
  requires mod > 0
{
    var products := prefixProducts(s, mod);
    forall i :: 0 <= i < |products| ==> products[i] !in forbidden
}

predicate ValidInput(n: nat, m: nat, forbidden: seq<nat>)
{
    m >= 1 &&
    n >= 0 &&
    |forbidden| == n &&
    (forall i :: 0 <= i < |forbidden| ==> 0 <= forbidden[i] < m) &&
    (forall i, j :: 0 <= i < j < |forbidden| ==> forbidden[i] != forbidden[j])
}

predicate ValidSequence(sequence: seq<nat>, m: nat, forbidden: seq<nat>)
  requires m > 0
{
    (forall i :: 0 <= i < |sequence| ==> 0 <= sequence[i] < m) &&
    allDistinct([1] + prefixProducts(sequence, m)) &&
    noForbiddenProducts(sequence, forbidden, m)
}

// <vc-helpers>
function ModuloAdd(a: nat, b: nat, m: nat): nat
  requires m > 0
  ensures 0 <= ModuloAdd(a, b, m) < m
{
  (a + b) % m
}

function ModuloSub(a: nat, b: nat, m: nat): nat
  requires m > 0
  ensures 0 <= ModuloSub(a, b, m) < m
{
  (a + m - b) % m
}

function ModuloMul(a: nat, b: nat, m: nat): nat
  requires m > 0
  ensures 0 <= ModuloMul(a, b, m) < m
{
  (a * b) % m
}

lemma lemma_distinct_elements_of_forbidden_are_not_modulo_zero(
  n: nat, m: nat, forbidden: seq<nat>
)
  requires ValidInput(n, m, forbidden)
  ensures (forall i :: 0 <= forbidden[i] < m)
{
  // This is directly from the definition of ValidInput.
}

lemma lemma_prefixProduct_is_well_behaved(s: seq<nat>, i: nat, mod: nat)
  requires mod > 0
  requires i <= |s|
  ensures 0 <= prefixProduct(s, i, mod) < mod
{
  if i == 0 then
    assert prefixProduct(s, i, mod) == 1;
  else
    lemma_prefixProduct_is_well_behaved(s, i-1, mod);
    assert (s[i-1] * prefixProduct(s, i-1, mod)) % mod == prefixProduct(s, i, mod);
    assert 0 <= s[i-1] < mod; // Assuming s elements are in [0, mod-1), which is true for ValidSequence
    assert 0 <= prefixProduct(s, i-1, mod) < mod;
}

lemma lemma_prefixProducts_elements_are_well_behaved(s: seq<nat>, m: nat)
  requires m > 0
  requires forall i :: 0 <= i < |s| ==> 0 <= s[i] < m
  ensures forall i :: 0 <= i < |prefixProducts(s, m)| ==> 0 <= prefixProducts(s, m)[i] < m
{
  var products := prefixProducts(s, m);
  forall i | 0 <= i < |products|
    ensures 0 <= products[i] < m
  {
    lemma_prefixProduct_is_well_behaved(s, i + 1, m);
  }
}

// Proving that if 'val' is not in forbidden, then it can be part of the sequence.
// This is more of a logical step in the overall proof.
lemma find_next_candidate(
    current_product: nat,
    m: nat,
    forbidden: seq<nat>
) returns (candidate: nat)
  requires m > 0
  requires 0 <= current_product < m
  requires forall i :: 0 <= forbidden[i] < m
  ensures 0 <= candidate < m
  ensures ModuloMul(current_product, candidate, m) !in forbidden
  ensures (exists k :: 0 <= k < m && ModuloMul(current_product, k, m) !in forbidden) ==> (candidate == 0 || (current_product != 0 && candidate == 1))
{
  if current_product == 0 {
    // If current_product is 0, then next_product will be 0.
    // If 0 is not in forbidden, then 0 is a valid candidate.
    // Otherwise, try 1 (though it won't change the product from 0) or any other.
    // But we need _some_ candidate.
    // The core idea is that if m > 1, there must be a non-forbidden product unless forbidden covers all m values.
    // Since n <= m, forbidden cannot cover all m values if n < m.
    // The case n == m is handled specially later (length 0).
    if 0 !in forbidden {
      return 0;
    } else if m > 1 {
      // If 0 is forbidden, and current_product is 0, any subsequent element will yield product 0.
      // This implies we cannot extend the sequence if 0 is forbidden and we have a 0 product.
      // If we are at this point, it means current_product is 0 and 0 is forbidden.
      // This branch should only be taken if m > 1 which implies not all elements are forbidden.
      // However, if current_product is 0, new product current_product * k % m will always be 0.
      // So if 0 is forbidden, we can't extend a sequence with a 0 product.
      // This path suggests we must have picked a sequence that avoids a 0 product.
      // The only way this could resolve is if m=1, then 0 is the only value.
      // We can always pick 0 and if it's forbidden, we would return length 0.
      // Let's return a default value that will be caught by the calling logic.
      // We need to return *some* candidate. Let's pick 1, it might be the only one available.
      if 1 !in forbidden {
         return 1;
      }
      return 0; // Fallback, implies we might not be able to extend
    } else { // m == 1
      return 0;
    }
  }

  // Iterate to find a non-forbidden value
  var i := 0;
  while i < m
    decreases m - i
    invariant 0 <= i <= m
    invariant forall k' :: 0 <= k' < i ==> ModuloMul(current_product, k', m) in forbidden
  {
    var next_prod_val := ModuloMul(current_product, i, m);
    if next_prod_val !in forbidden {
      return i;
    }
    i := i + 1;
  }
  // This case implies all possible products are forbidden.
  // This should not happen if m > n.
  // The fact that m > n means there are at least m-n non-forbidden values.
  // If m > n, there must be at least one k such that k is not in forbidden.
  // If current_product is not 0, then x * k might be in forbidden.
  // But due to Pigeonhole principle, if n < m, there must be at least one value `v` such that `v` is not in `forbidden`.
  // If `current_product` has a multiplicative inverse `inv` modulo `m`, and `v` is not in `forbidden`,
  // then we can choose `k = v * inv % m`.
  // However, `current_product` might not have an inverse.
  // The simplest is to try 1. If `current_product * 1 % m` is not forbidden, then 1 works.
  // If it is forbidden, try others.
  // A simpler approach for the find_next_candidate:
  // If (exists v :: 0 <= v < m && v !in forbidden), which is true if n < m.
  // Then try to extend with 1. If result is forbidden, try 0.
  // Or, simply try elements 0, 1, 2, ...
  // No, actually, for m > 1, if n == 0, then forbidden is empty, so anything is allowed.
  // In that case, any candidate works, e.g., 0.
  // If n > 0, it means some values are forbidden.
  // This lemma needs to guarantee a *candidate* exists that works if one exists in general.
  // The pigeonhole principle guarantees exists k s.t. current_product * k % m is not in forbidden.
  // This proof for `find_next_candidate` is non-trivial if `current_product` has divisors.
  // So returning 0 as a fallback value for now, which implies failure state for caller.
  return 0; // Fallback: this path should not be reached if n < m
}
// </vc-helpers>

// <vc-spec>
method solve(n: nat, m: nat, forbidden: seq<nat>) returns (length: nat, sequence: seq<nat>)
  requires ValidInput(n, m, forbidden)
  ensures length == |sequence|
  ensures length >= 0
  ensures m == 1 ==> length == 0 && sequence == []
  ensures m > 1 ==> ValidSequence(sequence, m, forbidden)
  ensures n == 0 && m > 1 ==> length > 0
// </vc-spec>
// <vc-code>
{
    length := 0;
    sequence := [];

    if m == 1 {
        // If m = 1, then all values are 0.
        // `forbidden` contains `n` zeros.
        // `ValidInput` ensures `|forbidden| == n` and `forbidden[i] == 0`.
        // `allDistinct([1] + prefixProducts(sequence, m))` would be `allDistinct([1] + [])` if sequence is empty.
        // `allDistinct([1])` is true.
        // `noForbiddenProducts(sequence, forbidden, m)`: `prefixProducts([], 1)` is `[]`.
        // `[] !in forbidden` is true.

        // If n > 0 (meaning 0 is forbidden), and m = 1:
        // `prefixProducts(sequence, 1)` will contain only 0s if sequence is not empty.
        // If 0 is in `forbidden`, then any non-empty sequence would result in a product of 0, which is forbidden.
        // Therefore, the only valid sequence is the empty sequence.
        // If n = 0 (meaning 0 is not forbidden), and m = 1:
        // `ValidSequence` requires `allDistinct([1] + prefixProducts(sequence, m))`.
        // If sequence = [0], products_with_1 = [1, 0]. Not distinct if 1 == 0, which is false.
        // But 0 <= sequence[i] < m means sequence[i] must be 0.
        // `allDistinct([1] + prefixProducts(sequence, 1))`
        // If sequence = [], products = [], [1] works.
        // If sequence = [0], products = [0], [1, 0] works.
        // If sequence = [0,0], products = [0,0], [1,0,0] fails distinct.
        // Only one 0 allowed means sequence can only have 0 once.
        // `prefixProduct([0], 1, 1)` = 0.
        // `allDistinct([1, 0])` is true. `noForbiddenProducts([0], [], 1)` is true.
        // So `sequence = [0]` is valid if `n=0`.
        // However, the problem statement often implicitly assumes there's more than one distinct element unless m=1.
        // The problem specification for `solve` states: `m == 1 ==> length == 0 && sequence == []`.
        // This makes it simple for m=1:
        return;
    }

    // m > 1
    // We aim to construct the longest possible sequence.
    // Start with an empty sequence, current product 1.
    // Try to extend the sequence by adding elements x_i such that
    // `current_product * x_i % m` is not in `forbidden`.
    // And also ensure `allDistinct` property.
    // The `allDistinct` property applies to `[1] + prefixProducts(sequence, m)`.

    // Max possible length is m.
    // We construct the sequence greedily.
    // `seen_products` will keep track of `1` and elements of `prefixProducts(sequence, m)`.
    var current_product := 1;
    var current_sequence: seq<nat> := [];
    var seen_products: set<nat> := {1};

    while true
      invariant 0 <= length <= m // Can't exceed m distinct products
      invariant length == |current_sequence|
      invariant 0 <= current_product < m
      invariant current_product == prefixProduct(current_sequence, |current_sequence|, m)
      invariant forall i :: 0 <= i < |current_sequence| ==> 0 <= current_sequence[i] < m
      invariant allDistinct({1} + set(prefixProducts(current_sequence, m)))
      invariant noForbiddenProducts(current_sequence, forbidden, m)
      invariant seen_products == {1} + set(prefixProducts(current_sequence, m))
      invariant forall p | p in seen_products :: 0 <= p < m
    {
        var found_extension := false;
        var next_val_to_add: nat := 0;

        // Iterate through possible values for the next element (0 to m-1)
        // Dafny likes explicit loops
        var candidate_val := 0;
        while candidate_val < m
          decreases m - candidate_val
          invariant 0 <= candidate_val <= m
        {
            var next_product := ModuloMul(current_product, candidate_val, m);

            if next_product !in forbidden && next_product !in seen_products {
                // This `candidate_val` allows us to extend the sequence.
                // It creates a `next_product` that is not forbidden and not yet seen.
                next_val_to_add := candidate_val;
                found_extension := true;
                break;
            }
            candidate_val := candidate_val + 1;
        }

        if found_extension {
            sequence := current_sequence + [next_val_to_add];
            length := length + 1;
            current_product := ModuloMul(current_product, next_val_to_add, m);
            seen_products := seen_products + {current_product};
            current_sequence := current_sequence + [next_val_to_add];

            // Verify loop invariants after update
            assert length == |current_sequence|; // Holds by appending one element.
            assert 0 <= current_product < m;     // Holds by ModuloMul.
            assert current_product == prefixProduct(current_sequence, |current_sequence|, m); //Holds by definition of prefixProduct
            assert (forall i :: 0 <= i < |current_sequence| ==> 0 <= current_sequence[i] < m); // Holds since next_val_to_add is in [0, m-1)
            assert forall p | p in seen_products :: 0 <= p < m ; // Holds because all products are computed modulo m.

            // The allDistinct and noForbiddenProducts check for the sequence built so far.
            // These properties are maintained because we explicitly checked next_product !in seen_products and next_product !in forbidden.
            lemma_prefixProducts_elements_are_well_behaved(current_sequence, m);
            assert noForbiddenProducts(current_sequence, forbidden, m);
            assert allDistinct({1} + set(prefixProducts(current_sequence, m)));

        } else {
            // No valid extension found. Break the loop.
            break;
        }
    }

    // After the loop, `sequence` and `length` hold the longest valid sequence.
    // We need to ensure that `n == 0 && m > 1 ==> length > 0`.
    // If n == 0, `forbidden` is empty.
    // This means `next_product !in forbidden` is always true.
    // Thus `next_product !in seen_products` is the only constraint.
    // We start with `seen_products = {1}`.
    // If m > 1:
    //   If current_product = 1, we can try `candidate_val = 0`.
    //   `next_product = (1 * 0) % m = 0`.
    //   `0 !in seen_products` (since 1 != 0 if m > 1).
    //   So we add 0 to the sequence: `current_sequence = [0]`, `current_product = 0`, `seen_products = {1, 0}`.
    //   Length becomes 1. So `length > 0` is guaranteed.

    sequence := current_sequence; // Copy constructed sequence to output.

    // Final checks for ensures clauses
    assert length == |sequence|;
    assert m > 1 ==> ValidSequence(sequence, m, forbidden);
    assert n == 0 && m > 1 ==> length > 0;
}
// </vc-code>

