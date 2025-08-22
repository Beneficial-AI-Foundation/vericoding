//ATOM
function SumL(s:seq<int>):int
{
  if (s==[]) then 0
  else s[0]+SumL(s[1..])
}


//ATOM
function SumR(s:seq<int>):int
{
  if (s==[]) then 0
  else SumR(s[..|s|-1])+s[|s|-1]
}


//IMPL sumElemsB

method sumElemsB(v:array<int>) returns (sum:int)
ensures sum==SumR(v[0..v.Length])
{
  sum := 0;
  var i := v.Length;
  while i > 0
    invariant 0 <= i <= v.Length
    invariant sum == SumR(v[i..v.Length])
  {
    i := i - 1;
    /* code modified by LLM (iteration 3): Correctly establish the relationship between SumR of consecutive slices */
    
    // Before adding v[i], we have: sum == SumR(v[i+1..v.Length])
    // We want to show: sum + v[i] == SumR(v[i..v.Length])
    
    if i + 1 == v.Length {
      // Case: v[i+1..v.Length] is empty, v[i..v.Length] contains only v[i]
      assert v[i+1..v.Length] == [];
      assert SumR(v[i+1..v.Length]) == 0;
      assert v[i..v.Length] == [v[i]];
      assert SumR([v[i]]) == SumR([]) + v[i] == 0 + v[i] == v[i];
    } else {
      // Case: v[i+1..v.Length] is non-empty
      // SumR(v[i..v.Length]) = SumR(v[i..v.Length-1]) + v[v.Length-1]
      // But v[i..v.Length-1] = [v[i]] + v[i+1..v.Length-1]
      // We need to use the fact that v[i..v.Length] extends v[i+1..v.Length] by prepending v[i]
      
      assert v[i..v.Length] != [];
      assert |v[i..v.Length]| == v.Length - i;
      assert v[i..v.Length][|v[i..v.Length]|-1] == v[v.Length-1];
      assert v[i..v.Length][..|v[i..v.Length]|-1] == v[i..v.Length-1];
      
      // Key insight: v[i..v.Length-1] = [v[i]] + v[i+1..v.Length-1]
      // And v[i+1..v.Length] = v[i+1..v.Length-1] + [v[v.Length-1]]
      
      assert SumR(v[i..v.Length]) == SumR(v[i..v.Length-1]) + v[v.Length-1];
      
      // We need a helper fact about how SumR distributes
      assert v[i+1..v.Length] != [] ==> SumR(v[i+1..v.Length]) == SumR(v[i+1..v.Length-1]) + v[v.Length-1];
    }
    
    sum := sum + v[i];
  }
}