// <vc-preamble>
function ListToNat(l: seq<nat>): nat
    decreases |l|
{
    if |l| == 0 then
        0
    else
        l[0] + 10 * ListToNat(l[1..])
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): power-of-10 function */
function pow10(n: int): nat
  requires n >= 0
  decreases n
{
  if n == 0 then 1 else 10 * pow10(n - 1)
}

/* helper modified by LLM (iteration 4): div-mod decomposition lemma */
lemma DivMod(s: nat)
  ensures s == s % 10 + 10 * (s / 10)
  ensures 0 <= s % 10 < 10
{
  var r := s % 10;
  var q := s / 10;
  assert s == r + 10 * q;
  assert 0 <= r < 10;
}

/* helper modified by LLM (iteration 4): lemma for appending a digit to a little-endian digit sequence */
lemma ListToNat_Append(s: seq<nat>, x: nat)
  ensures ListToNat(s + [x]) == ListToNat(s) + pow10(|s|) * x
  decreases |s|
{
  if |s| == 0 {
    // ListToNat([x]) == x, ListToNat([]) == 0, pow10(0) == 1
    assert ListToNat([x]) == x;
    assert ListToNat([]) == 0;
    assert pow10(0) == 1;
  } else {
    var h := s[0];
    var t := s[1..];
    ListToNat_Append(t, x);
    assert ListToNat(s) == h + 10 * ListToNat(t);
    assert ListToNat(s + [x]) == h + 10 * ListToNat(t + [x]);
    assert pow10(|s|) == 10 * pow10(|t|);
    assert ListToNat(t + [x]) == ListToNat(t) + pow10(|t|) * x;
    assert h + 10 * (ListToNat(t) + pow10(|t|) * x) == (h + 10 * ListToNat(t)) + 10 * pow10(|t|) * x;
    assert (h + 10 * ListToNat(t)) + 10 * pow10(|t|) * x == ListToNat(s) + pow10(|s|) * x;
  }
}

/* helper modified by LLM (iteration 4): relate array suffix to head + 10 * tail */
lemma ArrayStep(l: array<nat>, i: int)
  requires 0 <= i < l.Length
  ensures ListToNat(l[i..]) == l[i] + 10 * ListToNat(l[i+1..])
{
  assert ListToNat(l[i..]) == l[i] + 10 * ListToNat(l[i+1..]);
}

// </vc-helpers>

// <vc-spec>
method AddTwoNumbers(l1: array<nat>, l2: array<nat>) returns (result: array<nat>)
    requires 
        l1.Length > 0 &&
        l2.Length > 0 &&
        (forall i :: 0 <= i < l1.Length ==> l1[i] < 10) &&
        (forall i :: 0 <= i < l2.Length ==> l2[i] < 10) &&
        (l1[l1.Length - 1] != 0 || (l1.Length == 1 && l1[0] == 0)) &&
        (l2[l2.Length - 1] != 0 || (l2.Length == 1 && l2[0] == 0))
    ensures
        result.Length > 0 &&
        ListToNat(result[..]) == ListToNat(l1[..]) + ListToNat(l2[..]) &&
        (forall i :: 0 <= i < result.Length ==> result[i] < 10) &&
        (result[result.Length - 1] != 0 || (l1.Length == 1 && l1[0] == 0 && l2.Length == 1 && l2[0] == 0 && result.Length == 1 && result[0] == 0))
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 4): digit-wise addition with carry, maintaining numeric invariant using helper lemmas */
  var m := l1.Length;
  var n := l2.Length;
  var k := if m > n then m else n;
  var temp := new nat[k + 1];
  var carry := 0;
  var i := 0;
  while i < k
    invariant 0 <= i <= k
    invariant 0 <= carry < 10
    invariant forall j :: 0 <= j < i ==> temp[j] < 10
    invariant ListToNat(temp[..i]) + pow10(i) * (carry + (if i < m then ListToNat(l1[i..]) else 0) + (if i < n then ListToNat(l2[i..]) else 0)) == ListToNat(l1[..]) + ListToNat(l2[..])
    decreases k - i
  {
    var d1 := if i < m then l1[i] else 0;
    var d2 := if i < n then l2[i] else 0;
    var carry_old := carry;
    var s := d1 + d2 + carry_old;
    DivMod(s);
    temp[i] := s % 10;
    carry := s / 10;

    // Relate array suffixes at i and i+1 when applicable
    if i < m { ArrayStep(l1, i); }
    if i < n { ArrayStep(l2, i); }

    // Use ListToNat_Append to express temp[..i+1]
    ListToNat_Append(temp[..i], temp[i]);
    assert ListToNat(temp[..i+1]) == ListToNat(temp[..i]) + pow10(i) * temp[i];

    // Prepare old and new suffix expressions
    var A_old := if i < m then ListToNat(l1[i..]) else 0;
    var B_old := if i < n then ListToNat(l2[i..]) else 0;
    var A_new := if i + 1 < m then ListToNat(l1[i+1..]) else 0;
    var B_new := if i + 1 < n then ListToNat(l2[i+1..]) else 0;

    if i < m { assert A_old == d1 + 10 * A_new; } else { assert A_old == 0; }
    if i < n { assert B_old == d2 + 10 * B_new; } else { assert B_old == 0; }

    // from DivMod(s): s == temp[i] + 10 * carry
    assert s == temp[i] + 10 * carry;

    // arithmetic to re-establish the numeric invariant for i+1
    assert temp[i] + 10 * (carry + A_new + B_new) == carry_old + A_old + B_old;
    assert ListToNat(temp[..i+1]) + pow10(i+1) * (carry + A_new + B_new) == ListToNat(temp[..i]) + pow10(i) * (carry_old + A_old + B_old);

    i := i + 1;
  }

  temp[k] := carry;
  var finalLen := 0;
  if temp[k] == 0 {
    finalLen := k;
  } else {
    finalLen := k + 1;
  }

  result := new nat[finalLen];
  var idx := 0;
  while idx < finalLen
    invariant 0 <= idx <= finalLen
    invariant forall j :: 0 <= j < idx ==> result[j] == temp[j]
    decreases finalLen - idx
  {
    result[idx] := temp[idx];
    idx := idx + 1;
  }

  // Use loop invariant at i == k
  assert k >= m && k >= n;
  // suffixes beyond k are empty
  assert (if k < m then ListToNat(l1[k..]) else 0) == 0;
  assert (if k < n then ListToNat(l2[k..]) else 0) == 0;
  assert ListToNat(temp[..k]) + pow10(k) * carry == ListToNat(l1[..]) + ListToNat(l2[..]);

  // combine with stored carry in temp[k]
  assert temp[k] == carry;
  if finalLen == k + 1 {
    ListToNat_Append(temp[..k], temp[k]);
    assert ListToNat(temp[..k+1]) == ListToNat(temp[..k]) + pow10(k) * temp[k];
    assert ListToNat(result[..]) == ListToNat(temp[..k+1]);
  } else {
    assert temp[k] == 0;
    assert ListToNat(result[..]) == ListToNat(temp[..k]);
  }

  // Digit bounds
  assert forall j :: 0 <= j < result.Length ==> result[j] < 10;

  // Normalization: ensure top digit non-zero unless both inputs are zero
  if result.Length > 1 {
    assert result[result.Length - 1] != 0;
  } else {
    if result[0] == 0 {
      assert ListToNat(result[..]) == 0;
      assert ListToNat(l1[..]) + ListToNat(l2[..]) == 0;
    }
  }
}

// </vc-code>
