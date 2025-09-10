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
  // Helper lemma to reason about cycle reachability
}

lemma LemmaCycleOfLengthThreeExists(n: int, a: seq<int>, i: int, visited: set<int>)
  requires |a| == n
  requires forall k :: 0 <= k < n ==> 0 <= a[k] < n
  requires 0 <= i < n
  requires i in visited
  ensures exists j :: j in visited && a[a[j]] == j
  decreases n - |visited|
{
  // If we completed a cycle and it's not length 3, continue searching
  if a[a[i]] != i {
    var next := a[i];
    if next !in visited {
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
    invariant result == "NO" ==> !(exists j :: 0 <= j < i && HasLoveTriangleWith(n, a))
  {
    if !visited[i] {
      // Find cycle starting at i
      var current := i;
      var cycle := [];
      var seen : set<int> := {};
      
      while !visited[current] 
        invariant 0 <= current < n
        invariant forall x :: x in seen ==> 0 <= x < n
        invariant seen == set c | c in cycle
        invariant |cycle| <= n
        decreases n - |seen|
      {
        visited[current] := true;
        cycle := cycle + [current];
        seen := seen + {current};
        current := a[current];
      }
      
      // Check if we're part of a cycle that was already visited
      if current in seen {
        // Find the position where the cycle starts
        var cycle_start_index := 0;
        while cycle_start_index < |cycle| && cycle[cycle_start_index] != current 
          invariant 0 <= cycle_start_index <= |cycle|
        {
          cycle_start_index := cycle_start_index + 1;
        }
        
        if cycle_start_index < |cycle| {
          var cycle_length := |cycle| - cycle_start_index;
          
          // Check if we have a cycle of length 3
          if cycle_length == 3 {
            result := "YES";
            return;
          }
        }
      }
    }
    i := i + 1;
  }
}
// </vc-code>

