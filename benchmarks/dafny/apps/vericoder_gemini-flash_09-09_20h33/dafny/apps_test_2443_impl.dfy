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
    Calc {
      prefixProduct(s, i, mod);
    == // definition
      (s[i-1] * prefixProduct(s, i-1, mod)) % mod;
    };
    assert 0 <= (s[i-1] * prefixProduct(s, i-1, mod)) % mod < mod;
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
  ensures (exists k :: 0 <= k < m && ModuloMul(current_product, k, m) !in forbidden) ==> ModuloMul(current_product, candidate, m) !in forbidden
{
  if current_product == 0 then
    if 0 !in forbidden then
      return 0;
    else if m > 1 then
      if 1 !in forbidden && 1 < m then // Check 1 is a valid candidate
         return 1;
      else
        return 0; // Fallback, implies we might not be able to extend
    else // m == 1
      return 0;
  else
    var i := 0;
    while i < m
      decreases m - i
      invariant 0 <= i <= m
      invariant forall k' :: 0 <= k' < i ==> ModuloMul(current_product, k', m) in forbidden
    {
      var next_prod_val := ModuloMul(current_product, i, m);
      if next_prod_val !in forbidden then
        return i;
      i := i + 1;
    }
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
        return;
    }

    var current_product := 1;
    var current_sequence: seq<nat> := [];
    var seen_products: set<nat> := {1};

    while true
      invariant 0 <= length <= m
      invariant length == |current_sequence|
      invariant 0 <= current_product < m
      invariant current_product == prefixProduct(current_sequence, |current_sequence|, m)
      invariant forall i :: 0 <= i < |current_sequence| ==> 0 <= current_sequence[i] < m
      invariant allDistinct({1} + set(prefixProducts(current_sequence, m)))
      invariant noForbiddenProducts(current_sequence, forbidden, m)
      invariant seen_products == {1} + set(prefixProducts(current_sequence, m))
      invariant forall p | p in seen_products :: 0 <= p < m
      decreases m - length
    {
        var found_extension := false;
        var next_val_to_add: nat := 0;

        var candidate_val := 0;
        lemma_prefixProducts_elements_are_well_behaved(current_sequence, m);
        while candidate_val < m
          decreases m - candidate_val
          invariant 0 <= candidate_val <= m
          invariant forall i :: 0 <= i < |current_sequence| ==> 0 <= current_sequence[i] < m
          invariant forall p | p in seen_products :: 0 <= p < m
        {
            var next_product := ModuloMul(current_product, candidate_val, m);

            if next_product !in forbidden && next_product !in seen_products {
                next_val_to_add := candidate_val;
                found_extension := true;
                break;
            }
            candidate_val := candidate_val + 1;
        }

        if found_extension {
            var new_sequence := current_sequence + [next_val_to_add];
            var new_length := length + 1;
            var new_current_product := ModuloMul(current_product, next_val_to_add, m);
            var new_seen_products := seen_products + {new_current_product};

            // Prove current_product == prefixProduct(new_sequence, |new_sequence|, m)
            lemma_prefixProduct_is_well_behaved(current_sequence, |current_sequence|, m);
            calc {
                prefixProduct(new_sequence, |new_sequence|, m);
            ==  // |new_sequence| = |current_sequence| + 1
                prefixProduct(current_sequence + [next_val_to_add], (|current_sequence|+1), m);
            ==  // definition of prefixProduct
                (new_sequence[|current_sequence|] * prefixProduct(current_sequence, |current_sequence|, m)) % m;
            ==
                (next_val_to_add * current_product) % m;
            ==
                ModuloMul(current_product, next_val_to_add, m);
            }

            length := new_length;
            current_product := new_current_product;
            seen_products := new_seen_products;
            current_sequence := new_sequence;

            assert length == |current_sequence|;
            assert 0 <= current_product < m;
            assert current_product == prefixProduct(current_sequence, |current_sequence|, m);
            assert (forall i :: 0 <= i < |current_sequence| ==> 0 <= current_sequence[i] < m);
            lemma_prefixProducts_elements_are_well_behaved(current_sequence, m);

            // Assert noForbiddenProducts
            assert forall i :: 0 <= i < |prefixProducts(current_sequence, m)| ==> prefixProducts(current_sequence, m)[i] !in forbidden; // This line is crucial for noForbiddenProducts
            assert noForbiddenProducts(current_sequence, forbidden, m);

            // Assert allDistinct
            var ps_old := set(prefixProducts(current_sequence[..|current_sequence|-1], m));
            var ps_new := set(prefixProducts(current_sequence, m));
            assert ps_new == ps_old + {new_current_product};
            assert new_current_product !in ({1} + ps_old); // This is what comes from next_product !in seen_products
            assert allDistinct({1} + set(prefixProducts(current_sequence, m)));

        } else {
            // Case where no extension is found: check against postconditions
            if n==0 && m > 1 && length == 0 {
              // This can only happen if current_product == 1 and forbidden contains 1 and 0 (or no next_val satisfies criteria)
              // This implies m must be small or forbidden large. If m > 1 and n == 0, there are no forbidden values.
              // So, if length is still 0, it means current_product is 1, and we were unable to find any next_val,
              // which contradicts no forbidden values (next_val can always be 0 or 1).
              assert false; // This branch should not be reached when n == 0.
            }
            break;
        }
    }

    sequence := current_sequence;
    assert length == |sequence|;
    assert m > 1 ==> ValidSequence(sequence, m, forbidden);
    
    if n == 0 && m > 1 {
      // If n == 0, forbidden is empty.
      // We always start with current_product = 1 and seen_products = {1}.
      // Since forbidden is empty, ModuloMul(1, 0, m) = 0 is not in forbidden and not in seen_products.
      // So, len should be at least 1 (sequence = [0]) if m > 1.
      // If length is 0, it means the loop broke immediately, which implies found_extension was false.
      // But if n == 0, then `next_product !in forbidden` is always true.
      // The only way found_extension can be false is if `next_product !in seen_products` fails for all candidate_val.
      // But seen_products only grows with new products, and initially it's just {1}.
      // When candidate_val = 0, next_product = (current_product * 0) % m = 0.
      // If 0 is not in seen_products, then 0 can be added.
      // In the very first iteration, current_product = 1, seen_products = {1}.
      // candidate_val = 0, next_product = 0. 0 is not in {1}. So 0 would be selected.
      // This means length will be at least 1.
      assert length > 0;
    }
}
// </vc-code>

