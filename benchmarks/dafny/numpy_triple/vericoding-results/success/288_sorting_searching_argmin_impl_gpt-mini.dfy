// <vc-preamble>
// Method that returns the index of the minimum value in a non-empty array
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): removed null check and proved subset property for prefix minima */
lemma PrefixMinSubset(a: array<real>, cur: nat, k: nat)
  requires 0 <= k <= cur < a.Length
  requires forall j :: 0 <= j <= cur ==> a[cur] <= a[j]
  ensures forall j :: 0 <= j <= k ==> a[cur] <= a[j]
{
  var j := 0;
  while j <= k
    invariant 0 <= j <= k+1
    invariant forall t :: 0 <= t < j ==> a[cur] <= a[t]
  {
    assert a[cur] <= a[j];
    j := j + 1;
  }
}

/* helper modified by LLM (iteration 3): transitivity lemma for '<' and '<=' on reals */
lemma LessLeTrans(x: real, y: real, z: real)
  requires x < y
  requires y <= z
  ensures x < z
{
}

/* helper modified by LLM (iteration 3): convert strict inequality to non-strict for reals */
lemma LtImplLe(x: real, y: real)
  requires x < y
  ensures x <= y
{
}

// </vc-helpers>

// <vc-spec>
method numpy_argmin(a: array<real>) returns (index: nat)
  // Precondition: array must be non-empty
  requires a.Length > 0
  // Postcondition: returned index is valid
  ensures 0 <= index < a.Length
  // Postcondition: element at returned index is minimum among all elements
  ensures forall j :: 0 <= j < a.Length ==> a[index] <= a[j]
  // Postcondition: for ties, returns the first occurrence (smallest index)
  ensures forall j :: 0 <= j < a.Length && a[j] == a[index] ==> index <= j
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): linear scan with inner proof for preserving prefix minima */
  var i := 1;
  index := 0;
  while i < a.Length
    invariant 1 <= i <= a.Length
    invariant 0 <= index < a.Length
    invariant index < i
    invariant forall j :: 0 <= j < i ==> a[index] <= a[j]
    invariant forall j :: 0 <= j < i && a[j] == a[index] ==> index <= j
  {
    if a[i] < a[index] {
      var j := 0;
      while j < i
        invariant 0 <= j <= i
        invariant forall t :: 0 <= t < j ==> a[i] <= a[t]
      {
        assert a[index] <= a[j];
        LessLeTrans(a[i], a[index], a[j]);
        LtImplLe(a[i], a[j]);
        j := j + 1;
      }
      // trivial for j == i
      assert a[i] <= a[i];
      index := i;
    }
    i := i + 1;
  }
}

// </vc-code>
