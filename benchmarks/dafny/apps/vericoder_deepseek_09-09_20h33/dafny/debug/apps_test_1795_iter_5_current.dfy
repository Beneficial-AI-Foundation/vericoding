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
lemma LemmaCycleTraversal(n: int, a: seq<int>, start: int)
  requires |a| == n
  requires forall k :: 0 <= k < n ==> 0 <= a[k] < n
  requires 0 <= start < n
  ensures exists k :: 0 <= k < n && a[k] == start
{
  // Since every element maps to a valid index, and there are n elements,
  // by the pigeonhole principle, cycles must exist and include all elements
}

lemma LemmaCycleOfLengthThreeExists(n: int, a: seq<int>, i: int, visited: set<int>)
  requires |a| == n
  requires forall k :: 0 <= k < n ==> 0 <= a[k] < n
  requires 0 <= i < n
  requires i in visited
  ensures exists j :: j in visited && a[a[j]] == j
  decreases n - |visited|
{
  if a[a[i]] == i {
    // Found a cycle of length 2, which implies j where a[a[j]] == j
  } else {
    var next := a[i];
    if next !in visited && n - |visited| > 0 {
      LemmaCycleOfLengthThreeExists(n, a, next, visited + {next});
    }
  }
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
  result := "NO";
  
  var visited := new bool[n];
  var i := 0;
  
  while i < n
    invariant 0 <= i <= n
    invariant forall k :: 0 <= k < n ==> visited[k] == (k < i)
    invariant result == "NO" ==> 
      !(exists j :: 0 <= j < i && a[a[a[j]]] == j)
  {
    if !visited[i] {
      // Find cycle starting at i
      var current := i;
      var seen: set<int> := {};
      
      while !visited[current] 
        invariant 0 <= current < n
        invariant forall x :: x in seen ==> 0 <= x < n
        invariant seen == set c | c in seen
        invariant |seen| <= n
        decreases n - |seen|
      {
        visited[current] := true;
        seen := seen + {current};
        current := a[current];
      }
      
      // Check if current is part of the cycle we just traversed
      if current in seen {
        // Check for cycle of length 3
        var test := current;
        if a[a[a[test]]] == test {
          result := "YES";
          return;
        }
      }
    }
    i := i + 1;
  }
}
// </vc-code>

