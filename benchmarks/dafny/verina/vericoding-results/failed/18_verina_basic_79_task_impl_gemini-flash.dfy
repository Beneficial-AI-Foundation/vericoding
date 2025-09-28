// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): No changes needed. */
lemma AllPrecedingAreLeMax(a: array<int>, k: int, max_val: int)
  requires 0 <= k <= a.Length
  requires forall i :: 0 <= i < k ==> a[i] <= max_val
  ensures forall i :: 0 <= i < k ==> a[i] <= max_val
{
  // This lemma is trivially true by definition of forall.
  // No implementation needed.
}
// </vc-helpers>

// <vc-spec>
method OnlineMax(a: array<int>, x: int) returns (result: (int, int))
    requires
        a.Length > 0 &&
        x < a.Length
    ensures
        var (m, p) := result;
        x <= p && p < a.Length &&
        (forall i :: 0 <= i < x ==> a[i] <= m) &&
        (exists i :: 0 <= i < x && a[i] == m) &&
        ((p < a.Length - 1) ==> (exists i :: x <= i <= p && a[i] > m)) &&
        ((forall i :: x <= i < a.Length ==> a[i] <= m) ==> p == a.Length - 1)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Corrected logic for final_p when m_prefix is the overall max. */
{
  var m_prefix := a[0];
  var p_prefix := 0;

  var j := 1;
  while j < x
    invariant 0 < j <= x
    invariant 0 <= p_prefix < j
    invariant m_prefix == a[p_prefix]
    invariant (forall k_inv :: 0 <= k_inv < j ==> a[k_inv] <= m_prefix)
    decreases x - j
  {
    if a[j] > m_prefix {
      m_prefix := a[j];
      p_prefix := j;
    }
    j := j + 1;
  }

  var m_suffix := a[x];
  var p_suffix := x;
  var k := x + 1;
  while k < a.Length
    invariant x <= p_suffix < k
    invariant m_suffix == a[p_suffix]
    invariant (forall l :: x <= l < k ==> a[l] <= m_suffix)
    decreases a.Length - k
  {
    if a[k] > m_suffix {
      m_suffix := a[k];
      p_suffix := k;
    }
    k := k + 1;
  }

  var final_m: int;
  var final_p: int;

  if m_suffix > m_prefix {
    final_m := m_suffix;
    final_p := p_suffix;
  } else if m_prefix > m_suffix {
    final_m := m_prefix;
    final_p := p_prefix;
  } else { // m_prefix == m_suffix
    final_m := m_prefix;
    final_p := p_prefix;
    // Check if m_prefix also appears in the suffix part at a later index k
    k := x;
    while k < a.Length
      invariant x <= k <= a.Length
      invariant final_m == m_prefix
      invariant (exists idx :: 0 <= idx < k && a[idx] == final_m) || (final_m == m_suffix && final_p == p_suffix)
      invariant (forall l :: 0 <= l < k ==> a[l] <= final_m)
      decreases a.Length - k
    {
      if a[k] == final_m {
        final_p := k;
      }
      k := k + 1;
    }
  }
  result := (final_m, final_p);
}
// </vc-code>
