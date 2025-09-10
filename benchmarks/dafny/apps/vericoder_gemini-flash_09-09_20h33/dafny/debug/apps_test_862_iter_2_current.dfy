predicate ValidInput(n: int, a: seq<int>) {
  n >= 2 && |a| == n && (forall i :: 0 <= i < n ==> a[i] >= 0)
}

function ComputeB(a: seq<int>, i: int): int
  requires 0 <= i < |a|
{
  a[i] - i
}

function ComputeC(n: int, b: int): int
  requires n >= 2
{
  if b < 0 then b / n else (b + n - 1) / n
}

function ComputeCC(n: int, a: seq<int>, i: int): int
  requires ValidInput(n, a) && 0 <= i < n
{
  var b := ComputeB(a, i);
  var c := ComputeC(n, b);
  n * c
}

predicate IsOptimalEntrance(n: int, a: seq<int>, entrance: int)
  requires ValidInput(n, a) && 1 <= entrance <= n
{
  var i := entrance - 1;
  forall j :: 0 <= j < n ==> 
    (var cci := ComputeCC(n, a, i);
     var ccj := ComputeCC(n, a, j);
     cci <= ccj && (cci < ccj || i <= j))
}

// <vc-helpers>
lemma lemma_optimal_entrance_is_unique(n: int, a: seq<int>)
  requires ValidInput(n, a)
  ensures exists /*!*/ entrance :: 1 <= entrance <= n && IsOptimalEntrance(n, a, entrance)
{
  var min_cc := ComputeCC(n, a, 0);
  var min_idx := 0;

  for i := 1 to n - 1
    invariant 0 <= i <= n
    invariant 0 <= min_idx < i
    invariant min_cc == ComputeCC(n, a, min_idx)
    invariant forall k :: 0 <= k < i ==> min_cc < ComputeCC(n, a, k) || (min_cc == ComputeCC(n, a, k) && min_idx <= k)
  {
    var current_cc := ComputeCC(n, a, i);
    if current_cc < min_cc {
      min_cc := current_cc;
      min_idx := i;
    } else if current_cc == min_cc {
      // do nothing, min_idx already represents the smallest index with this min_cc
    }
  }

  // Prove existence
  assert 1 <= min_idx + 1 <= n;
  assert IsOptimalEntrance(n, a, min_idx + 1);

  // Prove uniqueness
  forall entrance1, entrance2 | 
    1 <= entrance1 <= n && IsOptimalEntrance(n, a, entrance1) &&
    1 <= entrance2 <= n && IsOptimalEntrance(n, a, entrance2)
    ensures entrance1 == entrance2
  {
    var i1 := entrance1 - 1;
    var i2 := entrance2 - 1;

    // From IsOptimalEntrance(n, a, entrance1)
    assert ComputeCC(n, a, i1) <= ComputeCC(n, a, i2);
    assert ComputeCC(n, a, i1) < ComputeCC(n, a, i2) || i1 <= i2;

    // From IsOptimalEntrance(n, a, entrance2)
    assert ComputeCC(n, a, i2) <= ComputeCC(n, a, i1);
    assert ComputeCC(n, a, i2) < ComputeCC(n, a, i1) || i2 <= i1;

    if (ComputeCC(n, a, i1) < ComputeCC(n, a, i2)) {
      // This contradicts ComputeCC(n, a, i2) <= ComputeCC(n, a, i1)
      assert false;
    } else if (ComputeCC(n, a, i2) < ComputeCC(n, a, i1)) {
      // This contradicts ComputeCC(n, a, i1) <= ComputeCC(n, a, i2)
      assert false;
    } else { // ComputeCC(n, a, i1) == ComputeCC(n, a, i2)
      // We must have i1 <= i2 from IsOptimalEntrance(n, a, entrance1)
      // And i2 <= i1 from IsOptimalEntrance(n, a, entrance2)
      assert i1 == i2;
    }
  }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, a: seq<int>) returns (result: int)
  requires ValidInput(n, a)
  ensures 1 <= result <= n
  ensures IsOptimalEntrance(n, a, result)
// </vc-spec>
// <vc-code>
{
  lemma_optimal_entrance_is_unique(n, a);
  
  var min_cc := ComputeCC(n, a, 0);
  var min_idx := 0;

  for i := 1 to n - 1
    invariant 0 <= i <= n
    invariant 0 <= min_idx < i
    invariant min_cc == ComputeCC(n, a, min_idx)
    invariant forall k :: 0 <= k < i ==> min_cc < ComputeCC(n, a, k) || (min_cc == ComputeCC(n, a, k) && min_idx <= k)
  {
    var current_cc := ComputeCC(n, a, i);
    if current_cc < min_cc {
      min_cc := current_cc;
      min_idx := i;
    } else if current_cc == min_cc {
      // Prefer smaller index for tie-breaking by not updating if current_cc == min_cc
      // and min_idx is already smaller. The invariant captures this logic.
    }
  }

  result := min_idx + 1;
  assert 1 <= result <= n;

  // Prove that result is indeed an optimal entrance
  forall j :: 0 <= j < n 
    ensures (var cci := ComputeCC(n, a, min_idx);
             var ccj := ComputeCC(n, a, j);
             cci <= ccj && (cci < ccj || min_idx <= j))
  {
    var cci := ComputeCC(n, a, min_idx);
    var ccj := ComputeCC(n, a, j);

    if j < min_idx {
      // From the loop invariant: forall k :: 0 <= k < min_idx ==> min_cc < ComputeCC(n, a, k) || (min_cc == ComputeCC(n, a, k) && min_idx <= k)
      // Applying k = j:
      assert min_cc < ComputeCC(n, a, j) || (min_cc == ComputeCC(n, a, j) && min_idx <= j);
      if min_cc < ComputeCC(n, a, j) {
        assert cci < ccj;
      } else { // min_cc == ComputeCC(n, a, j)
        assert min_idx <= j;
        assert false; // This contradicts j < min_idx
      }
    } else if j == min_idx {
      assert cci == ccj;
      assert min_idx <= j;
    } else { // j > min_idx
      // The loop invariant ensures that min_cc is the optimal value up to 'i' (which becomes 'n' here).
      // If we consider the loop's state when 'i' was 'j', either min_idx was already smaller than j
      // and had a better or equal cc value, or min_idx was updated to j because j had a better cc value.
      // In either case, the value at min_idx must be less than or equal to the value at j,
      // and if they are equal, min_idx must be less than or equal to j.
      assert cci <= ccj;
      if cci == ccj {
        assert min_idx <= j;
      }
    }
  }
}
// </vc-code>

