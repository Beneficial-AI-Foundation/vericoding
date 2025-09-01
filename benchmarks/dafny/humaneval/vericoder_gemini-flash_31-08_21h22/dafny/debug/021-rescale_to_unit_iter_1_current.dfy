function affine(x: real, shift: real, scale: real) : real
    requires scale > 0.0
{
    (x + shift) / scale
}
function affine_seq(s: seq<real>, r: seq<real>, shift: real, scale: real) : bool
  requires scale > 0.0
  requires |r| == |s|
{
  forall i :: 0 <= i < |s| ==> r[i] == affine(s[i], shift, scale)
}

// <vc-helpers>
function max_real(s: seq<real>): real
  requires |s| > 0
{
  if |s| == 1 then s[0] else max(s[0], max_real(s[1..]))
}

function min_real(s: seq<real>): real
  requires |s| > 0
{
  if |s| == 1 then s[0] else min(s[0], min_real(s[1..]))
}

lemma min_max_bounds(s: seq<real>)
  requires |s| > 0
  ensures forall i :: 0 <= i < |s| ==> min_real(s) <= s[i] <= max_real(s)
{
  if |s| == 1 {
    // Base case: only one element, min and max are that element
  } else {
    // Inductive step
    min_max_bounds(s[1..]);
    assert min_real(s[1..]) <= s[1]; // Prove property for s[1]
    assert max_real(s[1..]) >= s[1];

    if s[0] < min_real(s[1..]) {
      assert min_real(s) == s[0];
    } else {
      assert min_real(s) == min_real(s[1..]);
    }

    if s[0] > max_real(s[1..]) {
      assert max_real(s) == s[0];
    } else {
      assert max_real(s) == max_real(s[1..]);
    }

    forall i | 0 <= i < |s|
      ensures min_real(s) <= s[i] <= max_real(s)
    {
      if i == 0 {
        assert min_real(s) <= s[0];
        assert s[0] <= max_real(s);
      } else {
        assert min_real(s[1..]) <= s[i] <= max_real(s[1..]);
        assert min_real(s) <= s[i];
        assert s[i] <= max_real(s);
      }
    }
  }
}
// </vc-helpers>

// <vc-spec>
method rescale_to_unit(s: seq<real>) returns (r : seq<real>)
  // pre-conditions-start
  requires |s| >= 2
  requires exists i, j : int :: (0 <= i < j < |s|) && s[i] != s[j]
  // pre-conditions-end
  // post-conditions-start
  ensures |r| == |s|
  ensures forall i : int :: 0 <= i < |s| ==> 0.0 <= r[i] <= 1.0
  ensures exists i : int :: 0 <= i < |s| && r[i] == 0.0
  ensures exists i : int :: 0 <= i < |s| && r[i] == 1.0
  ensures exists shift, scale :: scale > 0.0 && affine_seq(s, r, shift, scale)
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
    var min_s := min_real(s);
    var max_s := max_real(s);

    min_max_bounds(s); // prove bounds for min_s and max_s

    var shift: real := -min_s;
    var scale: real;

    if max_s == min_s {
        // This case is ruled out by `exists i, j :: (0 <= i < j < |s|) && s[i] != s[j]`
        // However, Dafny needs to know this.
        // The precondition implies that max_s > min_s, so division by zero is not an issue.
        // We can assert this explicitly if needed, but the compiler should deduce.
        // assert max_s > min_s;
        r := new real[|s|](_ => 0.0); // An arbitrary valid result if this path were reachable
        return r;
    } else {
        scale := max_s - min_s;
        // Prove scale > 0
        assert max_s > min_s by {
            var i0, j0: int;
            calc {
                (0 <= i0 < j0 < |s|) && s[i0] != s[j0];
                min_real(s) <= s[i0];
                s[j0] <= max_real(s);
            }
            if s[i0] < s[j0] {
                assert min_real(s) <= s[i0] < s[j0] <= max_real(s);
                assert max_real(s) - min_real(s) > 0.0;
            } else { // s[j0] < s[i0]
                assert min_real(s) <= s[j0] < s[i0] <= max_real(s);
                assert max_real(s) - min_real(s) > 0.0;
            }
        }
    }

    r := new real[|s|];
    forall i | 0 <= i < |s| {
        r[i] := affine(s[i], shift, scale);
    }

    assert |r| == |s|; // Postcondition 1

    forall i | 0 <= i < |s|
        ensures 0.0 <= r[i] <= 1.0
    {
        var val := s[i];
        assert min_s <= val <= max_s by { min_max_bounds(s); };
        assert 0.0 <= val + shift; // val + shift = val - min_s >= 0
        assert val + shift <= max_s + shift; // val + shift = val - min_s <= max_s - min_s = scale
        assert 0.0 <= (val + shift) / scale; // Since scale > 0
        assert (val + shift) / scale <= (max_s + shift) / scale; // (max_s - min_s) / (max_s - min_s) = 1.0
        assert (max_s + shift) / scale == 1.0; // because max_s + shift = max_s - min_s = scale
    }

    var min_idx: int;
    var max_idx: int;
    exists k :: 0 <= k < |s| && s[k] == min_s ensures min_idx == k;
    exists k :: 0 <= k < |s| && s[k] == max_s ensures max_idx == k;

    // Postcondition: exists i :: r[i] == 0.0
    assert exists i :: 0 <= i < |s| && r[i] == 0.0 by {
        // Find an index `min_idx` where s[min_idx] == min_s
        // (Such an index must exist because min_s is an element of s)
        var k_min_s: int := -1;
        for k := 0 to |s|
            decreases |s| - k
            invariant 0 <= k <= |s|
            invariant k_min_s == -1 || (0 <= k_min_s < k && s[k_min_s] == min_s)
        {
            if s[k] == min_s {
                k_min_s := k;
                break;
            }
        }
        assert k_min_s != -1;
        assert r[k_min_s] == affine(s[k_min_s], shift, scale);
        assert r[k_min_s] == (s[k_min_s] + shift) / scale;
        assert r[k_min_s] == (min_s + (-min_s)) / scale;
        assert r[k_min_s] == 0.0 / scale;
        assert r[k_min_s] == 0.0;
        assert exists i :: 0 <= i < |s| && r[i] == 0.0;
    }

    // Postcondition: exists i :: r[i] == 1.0
    assert exists i :: 0 <= i < |s| && r[i] == 1.0 by {
        // Find an index `max_idx` where s[max_idx] == max_s
        var k_max_s: int := -1;
        for k := 0 to |s|
            decreases |s| - k
            invariant 0 <= k <= |s|
            invariant k_max_s == -1 || (0 <= k_max_s < k && s[k_max_s] == max_s)
        {
            if s[k] == max_s {
                k_max_s := k;
                break;
            }
        }
        assert k_max_s != -1;
        assert r[k_max_s] == affine(s[k_max_s], shift, scale);
        assert r[k_max_s] == (s[k_max_s] + shift) / scale;
        assert r[k_max_s] == (max_s + (-min_s)) / scale;
        assert r[k_max_s] == (max_s - min_s) / (max_s - min_s);
        assert r[k_max_s] == 1.0;
        assert exists i :: 0 <= i < |s| && r[i] == 1.0;
    }

    // Postcondition: exists shift, scale :: scale > 0.0 && affine_seq(s, r, shift, scale)
    // The `shift` and `scale` variables are already defined above.
    // We need to prove `scale > 0.0` which was done earlier.
    // And `affine_seq(s, r, shift, scale)` is satisfied by the loop that constructed `r`.
    assert affine_seq(s, r, shift, scale);
}
// </vc-code>

