method encode_cyclic(s: seq<int>) returns (res: seq<int>) 
    // post-conditions-start
    ensures |s| == |res|
    ensures forall i :: 0 <= i < |s| - |s| % 3 ==> (i % 3 == 0 ==> res[i] == s[i + 1])
    ensures forall i :: 0 <= i < |s| - |s| % 3 ==> (i % 3 == 1 ==> res[i] == s[i + 1])
    ensures forall i :: 0 <= i < |s| - |s| % 3 ==> (i % 3 == 2 ==> res[i] == s[i - 2])
    ensures forall i :: |s| - |s| % 3 <= i < |s| ==> (res[i] == s[i])
    // post-conditions-end
{
  assume{:axiom} false;
}

// <vc-helpers>
lemma mod_lemma(a: int, b: int)
  requires b > 0
  ensures 0 <= a % b < b
{}
// </vc-helpers>

// <vc-spec>
method decode_cyclic(s: seq<int>) returns (res: seq<int>)
    // post-conditions-start
    ensures |s| == |res|
    ensures forall i :: |s| - |s| % 3 <= i < |s| ==> (res[i] == s[i])
    ensures forall i :: 0 <= i < |s| - |s| % 3 ==> (i % 3 == 0 ==> res[i] == s[i + 2])
    ensures forall i :: 0 <= i < |s| - |s| % 3 ==> (i % 3 == 1 ==> res[i] == s[i - 1])
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    var n := |s|;
    var res_arr := new int[n];

    // Handle the cyclic encoding for the first part of the sequence
    for i := 0 to n - (n % 3)
        invariant 0 <= i <= n - (n % 3)
        invariant forall j :: 0 <= j < i ==> (
            (j % 3 == 0 && j + 2 < n && res_arr[j] == s[j + 2]) ||
            (j % 3 == 1 && j - 1 >= 0 && res_arr[j] == s[j - 1]) ||
            (j % 3 == 2 && res_arr[j] == s[j])
        )
        // Add specific invariants for the three cases
        invariant forall j :: 0 <= j < i && j % 3 == 0 ==> j + 2 < n ==> res_arr[j] == s[j + 2]
        invariant forall j :: 0 <= j < i && j % 3 == 1 ==> j - 1 >= 0 ==> res_arr[j] == s[j - 1]
        invariant forall j :: 0 <= j < i && j % 3 == 2 ==> res_arr[j] == s[j]
    {
        if i % 3 == 0 {
            res_arr[i] := s[i + 2];
        } else if i % 3 == 1 {
            res_arr[i] := s[i - 1];
        } else { // i % 3 == 2
            res_arr[i] := s[i];
        }
    }

    // Handle the remainder of the sequence without cyclic encoding
    for i := n - (n % 3) to n
        invariant n - (n % 3) <= i <= n
        invariant forall j :: n - (n % 3) <= j < i ==> res_arr[j] == s[j]
    {
        res_arr[i] := s[i];
    }
    return res_arr;
}
// </vc-code>

