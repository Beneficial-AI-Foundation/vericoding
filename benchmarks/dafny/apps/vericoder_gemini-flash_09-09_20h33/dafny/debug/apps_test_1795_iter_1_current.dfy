predicate ValidInput(n: int, f: seq<int>)
{
    n >= 2 && n <= 5000 &&
    |f| == n &&
    forall i :: 0 <= i < |f| ==> 1 <= f[i] <= n && f[i] != i + 1
}

function ZeroIndexedArray(n: int, f: seq<int>): seq<int>
    requires ValidInput(n, f)
{
    seq(n, j requires 0 <= j < n => f[j] - 1)
}

predicate HasLoveTriangleWith(n: int, a: seq<int>)
    requires |a| == n
    requires forall k :: 0 <= k < n ==> 0 <= a[k] < n
{
    exists i {:trigger a[i], a[a[i]], a[a[a[i]]]} :: 0 <= i < n && 
        0 <= a[i] < n && 0 <= a[a[i]] < n && a[a[a[i]]] == i
}

predicate HasLoveTriangle(n: int, f: seq<int>)
    requires ValidInput(n, f)
{
    var a := ZeroIndexedArray(n, f);
    HasLoveTriangleWith(n, a)
}

// <vc-helpers>
predicate CanReach(current: int, target: int, a: seq<int>, visited: seq<bool>)
  requires 0 <= current < |a|
  requires 0 <= target < |a|
  requires |a| == |visited|
  requires forall k :: 0 <= k < |a| ==> (visited[k] || a[k] == current) // This needs revision for correctness.
{
  if current == target then
    true
  else if visited[current] then
    false
  else
    CanReach(a[current], target, a, visited[current := true])
}

predicate IsCyclicPath(start: int, current: int, pathLength: int, a: seq<int>, visited: seq<bool>)
  requires 0 <= start < |a|
  requires 0 <= current < |a|
  requires |a| == |visited|
  requires pathLength >= 0
  requires (pathLength == 0) == (start == current)
{
  if pathLength == 0 then
    forall i :: 0 <= i < |a| ==> !visited[i]
  else
    !visited[current] && IsCyclicPath(start, a[current], pathLength - 1, a, visited[current := true])
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, f: seq<int>) returns (result: string)
    requires ValidInput(n, f)
    ensures result == "YES" || result == "NO"
    ensures result == "YES" <==> HasLoveTriangle(n, f)
// </vc-spec>
// <vc-code>
{
    var a := ZeroIndexedArray(n, f);

    for i := 0 to n - 1
        invariant 0 <= i <= n
        invariant forall k :: 0 <= k < i ==> 
            !(exists j :: 0 <= j < n && a[a[a[j]]] == j && j == k)
    {
        if a[a[a[i]]] == i
        {
            return "YES";
        }
    }

    return "NO";
}
// </vc-code>

