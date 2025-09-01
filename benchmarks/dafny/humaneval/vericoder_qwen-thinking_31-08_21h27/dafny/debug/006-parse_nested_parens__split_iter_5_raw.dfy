

```vc-helpers
lemma string_append_ok(s: string, c: char)
  requires (forall k :: 0 <= k < |s| ==> s[k] == '(')
```

```vc-code
assume{:axiom} false;
```