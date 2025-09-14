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
lemma Lemma_ComputeC_properties(n: int, b: int)
  requires n >= 2
  ensures var c := ComputeC(n, b); n * c <= b + n - 1 && b < n * (c + 1)
{
  var c := ComputeC(n, b);
  if b < 0 {
    var r := b % n;
    assert b == n * c + r;
    assert 0 <= r < n;
    assert n * c == b - r;
    assert b - r <= b + n - 1;
    assert b < n * (c + 1) by {
      assert n * (c + 1) == n * c + n == b - r + n;
      assert b - r + n == b + (n - r);
      assert n - r >= 1;
    }
  } else {
    var r := (b + n - 1) % n;
    assert (b + n - 1) == n * c + r;
    assert 0 <= r < n;
    assert n * c <= (b + n - 1);
    assert b <= (b + n - 1) < n * c + n;
    assert b < n * (c + 1);
  }
}

lemma Lemma_ComputeCC_relation(n: int, a: seq<int>, i: int)
  requires ValidInput(n, a) && 0 <= i < n
  ensures ComputeCC(n, a, i) == n * ComputeC(n, a[i] - i)
  ensures var cci := ComputeCC(n, a, i); 
          var b := a[i] - i;
          cci <= b + n - 1 && b < cci + n
{
  var b := ComputeB(a, i);
  var c := ComputeC(n, b);
  var cci := ComputeCC(n, a, i);
  assert cci == n * c;
  Lemma_ComputeC_properties(n, b);
}

lemma Lemma_FindOptimalEntrance(n: int, a: seq<int>, current: int, best: int)
  requires ValidInput(n, a) && 0 <= current < n && 0 <= best < n
  requires (forall k :: 0 <= k < current ==> !(ComputeCC(n, a, k) < ComputeCC(n, a, best) || 
                                              (ComputeCC(n, a, k) == ComputeCC(n, a, best) && k < best)))
  requires !(ComputeCC(n, a, current) < ComputeCC(n, a, best) || 
             (ComputeCC(n, a, current) == ComputeCC(n, a, best) && current < best))
  ensures 0 <= best < n
  ensures (forall k :: 0 <= k < current + 1 ==> !(ComputeCC(n, a, k) < ComputeCC(n, a, best) || 
                                                  (ComputeCC(n, a, k) == ComputeCC(n, a, best) && k < best)))
{
  // The proof is trivial: the two preconditions together imply the postcondition.
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
  var best_index := 0;
  var i := 0;
  
  while i < n
    invariant 0 <= i <= n
    invariant 0 <= best_index < n
    invariant forall k :: 0 <= k < i ==> !(ComputeCC(n, a, k) < ComputeCC(n, a, best_index) || 
                                            (ComputeCC(n, a, k) == ComputeCC(n, a, best_index) && k < best_index))
  {
    if ComputeCC(n, a, i) < ComputeCC(n, a, best_index) || 
       (ComputeCC(n, a, i) == ComputeCC(n, a, best_index) && i < best_index) {
      best_index := i;
    }
    Lemma_FindOptimalEntrance(n, a, i, best_index);
    i := i + 1;
  }
  
  result := best_index + 1;
}
// </vc-code>

