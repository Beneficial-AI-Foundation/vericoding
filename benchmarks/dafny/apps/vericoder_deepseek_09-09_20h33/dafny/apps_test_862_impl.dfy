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
lemma ComputeCCNonNegative(n: int, a: seq<int>, i: int)
  requires ValidInput(n, a) && 0 <= i < n
  ensures ComputeCC(n, a, i) >= -n  // Relaxed to allow negative values
{
  var b := ComputeB(a, i);
  var c := ComputeC(n, b);
  
  assert a[i] >= 0;
  assert i < n;
  assert b >= -i >= -(n-1);
  
  if b < 0 {
    assert b >= -(n-1);
    assert b <= -1;
    assert b / n == -1;
    assert n * (b / n) == -n;
  } else {
    assert (b + n - 1) / n >= 0;
    assert n * ((b + n - 1) / n) >= 0;
  }
}

lemma ComputeCCMonotonic(n: int, a: seq<int>, i: int, j: int)
  requires ValidInput(n, a) && 0 <= i < n && 0 <= j < n
  requires ComputeB(a, i) <= ComputeB(a, j)
  ensures ComputeCC(n, a, i) <= ComputeCC(n, a, j)
{
  var bi := ComputeB(a, i);
  var bj := ComputeB(a, j);
  var ci := ComputeC(n, bi);
  var cj := ComputeC(n, bj);
  
  if bi < 0 {
    if bj < 0 {
      assert bi / n <= bj / n;
    } else {
      // bi <= bj, but bi < 0 and bj >= 0
      // ComputeCC for bi: n * (bi/n) = n * -1 = -n (since bi >= -(n-1))
      // ComputeCC for bj: n * ((bj + n - 1)/n) >= 0
      assert n * (bi / n) <= 0 <= n * ((bj + n - 1) / n);
    }
  } else {
    if bj < 0 {
      // This case shouldn't happen since bi >= 0 and bj < 0
      // But we have bi <= bj, contradiction
      assert false;
    } else {
      assert bi <= bj;
      assert (bi + n - 1) <= (bj + n - 1);
      assert (bi + n - 1) / n <= (bj + n - 1) / n;
    }
  }
}

lemma ComputeCCSameValueSameB(n: int, a: seq<int>, i: int, j: int)
  requires ValidInput(n, a) && 0 <= i < n && 0 <= j < n
  requires ComputeB(a, i) == ComputeB(a, j)
  ensures ComputeCC(n, a, i) == ComputeCC(n, a, j)
{
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
  var best := 0;
  var best_cc := ComputeCC(n, a, 0);
  
  var k := 1;
  while k < n
    invariant 1 <= k <= n
    invariant 0 <= best < n
    invariant best_cc == ComputeCC(n, a, best)
    invariant forall j :: 0 <= j < k ==> 
      best_cc <= ComputeCC(n, a, j) && 
      (best_cc < ComputeCC(n, a, j) || best <= j)
  {
    var current_cc := ComputeCC(n, a, k);
    if current_cc < best_cc {
      best := k;
      best_cc := current_cc;
    } else if current_cc == best_cc {
      if k < best {
        best := k;
        best_cc := current_cc;
      }
    }
    k := k + 1;
    
    // Add assertion to help verifier understand the invariant is maintained
    assert forall j :: 0 <= j < k ==> 
      best_cc <= ComputeCC(n, a, j) && 
      (best_cc < ComputeCC(n, a, j) || best <= j);
  }
  
  result := best + 1;
}
// </vc-code>

