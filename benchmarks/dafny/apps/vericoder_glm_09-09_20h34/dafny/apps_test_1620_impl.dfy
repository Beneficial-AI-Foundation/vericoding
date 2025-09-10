predicate ValidInput(n: int)
{
  n >= 1
}

predicate ValidOutput(s: string, n: int)
{
  |s| == n &&
  (forall i :: 0 <= i < |s| ==> s[i] == 'a' || s[i] == 'b' || s[i] == 'c') &&
  (forall i :: 0 <= i <= |s| - 3 ==> !(s[i] == s[i+2]))
}

predicate MinimalCUsage(s: string)
{
  forall i :: 0 <= i < |s| ==> s[i] == 'a' || s[i] == 'b'
}

// <vc-helpers>
lemma CheckCondition(s: array<char>, n: int)
    requires 0 < n
    requires s.Length == n
    requires forall i :: 0 <= i < n ==> 
        s[i] == if (i/2) % 2 == 0 then 'a' else 'b'
    ensures forall i :: 0 <= i < n-2 ==> s[i] != s[i+2]
{
    forall i | 0 <= i < n-2 
        ensures s[i] != s[i+2]
    {
        if i % 2 == 0 {
            var j := i / 2;
            if j % 2 == 0 {
                assert s[i] == 'a';
                assert (j+1) % 2 == 1;
                assert s[i+2] == 'b';
            } else {
                assert s[i] == 'b';
                assert (j+1) % 2 == 0;
                assert s[i+2] == 'a';
            }
        } else {
            var j := i / 2;
            if j % 2 == 0 {
                assert s[i] == 'a';
                assert (j+1) % 2 == 1;
                assert s[i+2] == 'b';
            } else {
                assert s[i] == 'b';
                assert (j+1) % 2 == 0;
                assert s[i+2] == 'a';
            }
        }
    }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int) returns (result: string)
  requires ValidInput(n)
  ensures ValidOutput(result, n)
  ensures MinimalCUsage(result)
// </vc-spec>
// <vc-code>
{
    var arr := new char[n];
    for i := 0 to n
        invariant 0 <= i <= n
        invariant forall j :: 0 <= j < i ==> 
            arr[j] == if (j/2) % 2 == 0 then 'a' else 'b'
    {
        if (i/2) % 2 == 0 {
            arr[i] := 'a';
        } else {
            arr[i] := 'b';
        }
    }
    CheckCondition(arr, n);
    result := arr[..];
}
// </vc-code>

