// <vc-preamble>
// Float datatype that can represent NaN for negative inputs
datatype Float = Real(value: real) | NaN

// Vector represented as a sequence with a fixed length
datatype Vector<T> = Vector(elements: seq<T>, length: nat)
{
    predicate Valid() {
        |elements| == length
    }
    
    function get(i: nat): T
        requires Valid()
        requires i < length
    {
        elements[i]
    }
}

// Helper predicate to check if a Float is non-negative
predicate NonNegative(x: Float) {
    x.Real? && x.value >= 0.0
}

// Helper predicate to check if a Float is NaN
predicate IsNaN(x: Float) {
    x.NaN?
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Added explicit proof steps for non-linear arithmetic. */
lemma SqrtMonotonic(r1: real, r2: real, s1: real, s2: real)
    requires 0.0 <= r1 <= r2
    requires s1 >= 0.0 && s1 * s1 == r1
    requires s2 >= 0.0 && s2 * s2 == r2
    ensures s1 <= s2
{
    if s1 > s2 {
        // Proof by contradiction. Assume s1 > s2.
        // We will show this implies r1 > r2, a contradiction.
        // From preconditions and the if-condition, we have s1 > s2 >= 0.0.
        assert s1 - s2 > 0.0;
        // Also, s1 > s2 >= 0.0 implies s1 > 0. Thus s1+s2 > s2+s2 >= 0.
        assert s1 + s2 > 0.0;

        // The product of two positive reals is positive. Dafny's SMT solver can handle this.
        calc {
            s1*s1 - s2*s2;
            == (s1 - s2) * (s1 + s2);
        }
        assert s1*s1 - s2*s2 > 0.0;
        assert s1*s1 > s2*s2;

        assert r1 > r2; // since s1*s1==r1 and s2*s2==r2
        // This contradicts the precondition r1 <= r2.
    }
}
// </vc-helpers>

// <vc-spec>
method sqrt(x: Vector<Float>) returns (result: Vector<Float>)
    requires x.Valid()
    ensures result.Valid()
    ensures result.length == x.length
    // For non-negative inputs: result² = input and result ≥ 0
    ensures forall i :: 0 <= i < x.length && x.get(i).Real? && x.get(i).value >= 0.0 ==>
        result.get(i).Real? && result.get(i).value * result.get(i).value == x.get(i).value && result.get(i).value >= 0.0
    // For negative inputs: result is NaN
    ensures forall i :: 0 <= i < x.length && x.get(i).Real? && x.get(i).value < 0.0 ==>
        result.get(i).NaN?
    // NaN inputs produce NaN outputs
    ensures forall i :: 0 <= i < x.length && x.get(i).NaN? ==>
        result.get(i).NaN?
    // Special cases
    ensures forall i :: 0 <= i < x.length && x.get(i).Real? && x.get(i).value == 0.0 ==>
        result.get(i).Real? && result.get(i).value == 0.0
    ensures forall i :: 0 <= i < x.length && x.get(i).Real? && x.get(i).value == 1.0 ==>
        result.get(i).Real? && result.get(i).value == 1.0
    // Monotonicity on non-negative inputs
    ensures forall i, j :: (0 <= i < x.length && 0 <= j < x.length &&
        x.get(i).Real? && x.get(j).Real? && 
        x.get(i).value >= 0.0 && x.get(j).value >= 0.0 && x.get(i).value <= x.get(j).value) ==>
        result.get(i).Real? && result.get(j).Real? && result.get(i).value <= result.get(j).value
    // Shape preservation is guaranteed by the length equality
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Used forall with ensures and handled special cases explicitly to aid verification. */
    var new_elements: seq<Float> := [];
    var i: nat := 0;
    while i < x.length
        invariant 0 <= i <= x.length
        invariant |new_elements| == i
        invariant forall k :: 0 <= k < i ==> (
            (x.get(k).Real? && x.get(k).value >= 0.0 ==> new_elements[k].Real? && new_elements[k].value >= 0.0 && new_elements[k].value * new_elements[k].value == x.get(k).value) &&
            (x.get(k).Real? && x.get(k).value < 0.0 ==> new_elements[k].NaN?) &&
            (x.get(k).NaN? ==> new_elements[k].NaN?)
        )
        invariant forall k, l :: (0 <= k < i && 0 <= l < i &&
                                  x.get(k).Real? && x.get(l).Real? &&
                                  x.get(k).value >= 0.0 && x.get(l).value >= 0.0 && x.get(k).value <= x.get(l).value) ==>
                                  (new_elements[k].Real? && new_elements[l].Real? && new_elements[k].value <= new_elements[l].value)
    {
        var current_float := x.get(i);
        var sqrt_float: Float;

        if current_float.Real? && current_float.value >= 0.0 {
            var v := current_float.value;
            var r: real;
            
            if v == 0.0 {
                r := 0.0;
            } else if v == 1.0 {
                r := 1.0;
            } else { // v > 0, v != 1, v != 0
                var r_exist: real :| r_exist >= 0.0 && r_exist * r_exist == v;
                r := r_exist;
            }
            sqrt_float := Real(r);
            
            if v > 0.0 { // For v=0, monotonicity is trivial as it's the minimum non-negative value.
                forall k | 0 <= k < i && x.get(k).Real? && x.get(k).value >= 0.0
                    ensures (x.get(k).value <= v ==> new_elements[k].value <= r) && (v <= x.get(k).value ==> r <= new_elements[k].value)
                {
                    var prev_v := x.get(k).value;
                    var prev_r := new_elements[k].value;
                    if prev_v <= v {
                        SqrtMonotonic(prev_v, v, prev_r, r);
                    } else { // v < prev_v
                        SqrtMonotonic(v, prev_v, r, prev_r);
                    }
                }
            }
        } else {
            sqrt_float := NaN;
        }

        new_elements := new_elements + [sqrt_float];
        i := i + 1;
    }
    result := Vector(new_elements, x.length);
}
// </vc-code>
