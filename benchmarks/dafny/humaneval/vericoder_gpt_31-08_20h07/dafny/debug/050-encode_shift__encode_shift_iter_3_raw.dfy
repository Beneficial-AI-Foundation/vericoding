```vc-helpers
lemma {:axiom} ExistsStr(u: seq<char>)
  ensures exists t: string :: |t| == |u| && forall i :: 0 <= i < |u| ==> t[i] == u[i]
```

```vc-code
{
  var u: seq<char> := [];
  var i := 0;
  while i < |s>
    invariant 0 <= i <= |s|
    invariant |u| == i
    invariant forall j :: 0 <= j < i ==> u[j] == encode_char(s[j])
    decreases |s| - i
  {
    u := u + [encode_char(s[i])];
    i := i + 1;
  }
  ExistsStr(u);
  t :| |t| == |u| && forall j :: 0 <= j < |u| ==> t[j] == u[j];
}
```