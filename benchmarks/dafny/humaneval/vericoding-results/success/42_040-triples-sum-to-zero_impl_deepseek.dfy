// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
predicate triple_sum_zero(l: seq<int>, i: int, j: int, k: int) {
  0 <= i < |l| && 0 <= j < |l| && 0 <= k < |l| && i != j && j != k && i != k && l[i] + l[j] + l[k] == 0
}

predicate no_triples_sum_to_zero(l: seq<int>) {
  forall i: int, j: int, k: int :: 0 <= i < |l| && 0 <= j < |l| && 0 <= k < |l| && i != j && j != k && i != k ==> l[i] + l[j] + l[k] != 0
}
// </vc-helpers>

// <vc-spec>
method triples_sum_to_zero(l : seq<int>) returns (result : bool)

    ensures result ==> exists i : int, j : int, k : int :: 0 <= i < |l| && 0 <= j < |l| && 0 <= k < |l| && i != j && j != k && i != k && l[i] + l[j] + l[k] == 0
    ensures !result ==> forall i : int, j : int, k : int :: 0 <= i < |l| && 0 <= j < |l| && 0 <= k < |l| && i != j && j != k && i != k ==> l[i] + l[j] + l[k] != 0
// </vc-spec>
// <vc-code>
{
  var n := |l|;
  if n < 3 {
    result := false;
    return;
  }
  
  result := false;
  
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant !result ==> forall x: int, y: int, z: int :: 0 <= x < i && 0 <= y < n && 0 <= z < n && x != y && y != z && x != z ==> l[x] + l[y] + l[z] != 0
    decreases n - i
  {
    var j := 0;
    while j < n
      invariant 0 <= j <= n
      invariant !result ==> forall y: int, z: int :: 0 <= y < j && 0 <= z < n && i != y && i != z && y != z ==> l[i] + l[y] + l[z] != 0
      decreases n - j
    {
      if j == i {
        j := j + 1;
        continue;
      }
      
      var k := 0;
      while k < n
        invariant 0 <= k <= n
        invariant !result ==> forall z: int :: 0 <= z < k && i != z && j != z ==> l[i] + l[j] + l[z] != 0
        decreases n - k
      {
        if k == i || k == j {
          k := k + 1;
          continue;
        }
        
        if l[i] + l[j] + l[k] == 0 {
          result := true;
          return;
        }
        
        k := k + 1;
      }
      
      j := j + 1;
    }
    
    i := i + 1;
  }
}
// </vc-code>
