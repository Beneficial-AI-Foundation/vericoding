// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function mod3(n: int): int
  requires n >= 0
{
  if n < 3 then n else mod3(n - 3)
}

lemma cyclic_rotation_properties(i: int, len: int)
  requires 0 <= i < len - len % 3
  ensures (i % 3 == 0 ==> i + 2 < len - len % 3)
  ensures (i % 3 == 1 ==> i - 1 >= 0)
{
}
// </vc-helpers>

// <vc-spec>
method decode_cyclic(s: seq<int>) returns (res: seq<int>)

    ensures |s| == |res|
    ensures forall i :: |s| - |s| % 3 <= i < |s| ==> (res[i] == s[i])
    ensures forall i :: 0 <= i < |s| - |s| % 3 ==> (i % 3 == 0 ==> res[i] == s[i + 2])
    ensures forall i :: 0 <= i < |s| - |s| % 3 ==> (i % 3 == 1 ==> res[i] == s[i - 1])
// </vc-spec>
// <vc-code>
{
    res := s;
    var length := |s|;
    var effective_length := length - length % 3;
    
    var index := 0;
    while index < effective_length
      invariant 0 <= index <= effective_length
      invariant |res| == |s|
      invariant forall j :: 0 <= j < index ==> (j % 3 == 0 ==> res[j] == s[j + 2])
      invariant forall j :: 0 <= j < index ==> (j % 3 == 1 ==> res[j] == s[j - 1])
      invariant forall j :: effective_length <= j < |s| ==> res[j] == s[j]
    {
        if index % 3 == 0 {
            res := res[index := s[index + 2]];
        } else if index % 3 == 1 {
            res := res[index := s[index - 1]];
        }
        index := index + 1;
    }
  }
// </vc-code>
