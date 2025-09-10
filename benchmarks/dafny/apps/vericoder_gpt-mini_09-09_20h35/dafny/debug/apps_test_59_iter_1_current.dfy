predicate ValidInput(n: int, a: seq<int>, p: string)
{
    n >= 2 &&
    |a| == n &&
    |p| == n - 1 &&
    (forall i :: 0 <= i < |p| ==> p[i] == '0' || p[i] == '1') &&
    (forall i :: 0 <= i < |a| ==> 1 <= a[i] <= n) &&
    (forall i :: 1 <= i <= n ==> exists j :: 0 <= j < |a| && a[j] == i)
}

function max_up_to(a: seq<int>, i: int): int
    requires 0 <= i < |a|
    decreases i
{
    if i == 0 then a[0]
    else if a[i] > max_up_to(a, i-1) then a[i]
    else max_up_to(a, i-1)
}

predicate CanSort(n: int, a: seq<int>, p: string)
    requires ValidInput(n, a, p)
{
    forall i :: 0 <= i < n - 1 ==> 
        (p[i] == '0' ==> max_up_to(a, i) <= i + 1)
}

// <vc-helpers>
lemma MaxUpTo_step(a: seq<int>, i: int)
  requires 0 <= i
  requires i + 1 < |a|
  ensures max_up_to(a, i+1) == (if a[i+1] > max_up_to(a, i) then a[i+1] else max_up_to(a, i))
{
  // By unfolding the definition of max_up_to for index i+1.
  // Dafny accepts this lemma by trivial unfolding of the function body.
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, a: seq<int>, p: string) returns (result: string)
    requires ValidInput(n, a, p)
    ensures result == "YES" || result == "NO"
    ensures result == "YES" <==> CanSort(n, a, p)
// </vc-spec>
// <vc-code>
{
  var m := a[0];
  var ok := true;
  var i := 0;
  while i < n - 1
    invariant 0 <= i <= n - 1
    invariant m == max_up_to(a, i)
    invariant ok <==> (forall j :: 0 <= j < i ==> (p[j] == '0' ==> max_up_to(a, j) <= j + 1))
    invariant 1 <= m <= n
  {
    var cond := true;
    if p[i] == '0' && !(m <= i + 1) {
      cond := false;
    }
    ok := ok && cond;

    // update m to be max_up_to(a, i+1)
    var next := a[i + 1];
    if next > m {
      m := next;
    }
    MaxUpTo_step(a, i);
    assert m == max_up_to(a, i + 1);

    i := i + 1;
  }

  if ok {
    result := "YES";
  } else {
    result := "NO";
  }
}
// </vc-code>

