method CanyonSearch(a: array<int>, b: array<int>) returns (d:nat)
  requires a.Length !=0 && b.Length!=0
  requires forall i,j :: 0<=i<j<a.Length ==> a[i]<=a[j]
  requires forall i,j :: 0<=i<j<b.Length ==> b[i]<=b[j]
  ensures exists i,j:: 0<=i<a.Length && 0<=j<b.Length && d==if a[i] < b[j] then (b[j]-a[i]) else (a[i]-b[j])
  ensures forall i,j:: 0<=i<a.Length && 0<=j<b.Length ==> d<=if a[i] < b[j] then (b[j]-a[i]) else (a[i]-b[j])
// </vc-spec>
// <vc-code>
{
  var i := 0;
  var j := 0;
  var min_diff := if a[0] < b[0] then (b[0] - a[0]) else (a[0] - b[0]);
  var witness_i := 0;
  var witness_j := 0;
  
  while i < a.Length && j < b.Length
    invariant 0 <= i <= a.Length
    invariant 0 <= j <= b.Length
    invariant 0 <= witness_i < a.Length
    invariant 0 <= witness_j < b.Length
    invariant min_diff == if a[witness_i] < b[witness_j] then (b[witness_j] - a[witness_i]) else (a[witness_i] - b[witness_j])
    invariant forall ii, jj :: 0 <= ii < a.Length && 0 <= jj < b.Length && 
              (ii < i && jj < j)
              ==> min_diff <= if a[ii] < b[jj] then (b[jj] - a[ii]) else (a[ii] - b[jj])
  {
    var current_diff := if a[i] < b[j] then (b[j] - a[i]) else (a[i] - b[j]);
    
    if current_diff < min_diff {
      min_diff := current_diff;
      witness_i := i;
      witness_j := j;
    }
    
    if a[i] < b[j] {
      i := i + 1;
    } else {
      j := j + 1;
    }
  }
  
  // Handle remaining elements if one array is exhausted
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant j == b.Length
    invariant 0 <= witness_i < a.Length
    invariant 0 <= witness_j < b.Length
    invariant min_diff == if a[witness_i] < b[witness_j] then (b[witness_j] - a[witness_i]) else (a[witness_i] - b[witness_j])
    invariant forall ii, jj :: 0 <= ii < a.Length && 0 <= jj < b.Length && ii < i 
              ==> min_diff <= if a[ii] < b[jj] then (b[jj] - a[ii]) else (a[ii] - b[jj])
    invariant forall ii, jj :: 0 <= ii < a.Length && 0 <= jj < b.Length && ii < i && jj < j
              ==> min_diff <= if a[ii] < b[jj] then (b[jj] - a[ii]) else (a[ii] - b[jj])
  {
    var jj := 0;
    while jj < b.Length
      invariant 0 <= jj <= b.Length
      invariant 0 <= witness_i < a.Length
      invariant 0 <= witness_j < b.Length
      invariant min_diff == if a[witness_i] < b[witness_j] then (b[witness_j] - a[witness_i]) else (a[witness_i] - b[witness_j])
      invariant forall k :: 0 <= k < jj ==> min_diff <= if a[i] < b[k] then (b[k] - a[i]) else (a[i] - b[k])
    {
      var current_diff := if a[i] < b[jj] then (b[jj] - a[i]) else (a[i] - b[jj]);
      
      if current_diff < min_diff {
        min_diff := current_diff;
        witness_i := i;
        witness_j := jj;
      }
      jj := jj + 1;
    }
    
    i := i + 1;
  }
  
  while j < b.Length
    invariant 0 <= j <= b.Length
    invariant i == a.Length
    invariant 0 <= witness_i < a.Length
    invariant 0 <= witness_j < b.Length
    invariant min_diff == if a[witness_i] < b[witness_j] then (b[witness_j] - a[witness_i]) else (a[witness_i] - b[witness_j])
    invariant forall ii, jj :: 0 <= ii < a.Length && 0 <= jj < b.Length && jj < j 
              ==> min_diff <= if a[ii] < b[jj] then (b[jj] - a[ii]) else (a[ii] - b[jj])
    invariant forall ii, jj_old :: 0 <= ii < a.Length && 0 <= jj_old < b.Length && ii < i && jj_old < b.Length
              ==> min_diff <= if a[ii] < b[jj_old] then (b[jj_old] - a[ii]) else (a[ii] - b[jj_old])
  {
    var ii := 0;
    while ii < a.Length
      invariant 0 <= ii <= a.Length
      invariant 0 <= witness_i < a.Length
      invariant 0 <= witness_j < b.Length
      invariant min_diff == if a[witness_i] < b[witness_j] then (b[witness_j] - a[witness_i]) else (a[witness_i] - b[witness_j])
      invariant forall k :: 0 <= k < ii ==> min_diff <= if a[k] < b[j] then (b[j] - a[k]) else (a[k] - b[j])
    {
      var current_diff := if a[ii] < b[j] then (b[j] - a[ii]) else (a[ii] - b[j]);
      
      if current_diff < min_diff {
        min_diff := current_diff;
        witness_i := ii;
        witness_j := j;
      }
      ii := ii + 1;
    }
    
    j := j + 1;
  }
  
  d := min_diff;
}
// </vc-code>

// <vc-helpers>
// </vc-helpers>