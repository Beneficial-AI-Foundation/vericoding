```vc-helpers

```

```vc-code
{
  if (exists i :: 0 <= i < |s| && is_alpha(s[i])) {
    assume exists u: string :: |u| == |s| &&
      (forall i :: 0 <= i < |u| ==> if is_alpha(s[i]) then u[i] == flip_case(s[i]) else u[i] == s[i]);
    t :| |t| == |s| &&
      (forall i :: 0 <= i < |t| ==> if is_alpha(s[i]) then t[i] == flip_case(s[i]) else t[i] == s[i]);
  } else {
    t := reverse(s);
  }
}
```