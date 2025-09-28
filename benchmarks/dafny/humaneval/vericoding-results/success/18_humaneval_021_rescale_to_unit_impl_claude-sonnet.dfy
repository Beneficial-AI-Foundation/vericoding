// <vc-preamble>
function affine(x: real, shift: real, scale: real) : real
    requires scale > 0.0
{
    (x + shift) / scale
}
function affine_seq(s: seq<real>, r: seq<real>, shift: real, scale: real) : bool
  requires scale > 0.0
  requires |r| == |s|
{
  forall i :: 0 <= i < |s| ==> r[i] == affine(s[i], shift, scale)
}
// </vc-preamble>

// <vc-helpers>
function min_seq(s: seq<real>): real
  requires |s| > 0
  ensures exists i :: 0 <= i < |s| && min_seq(s) == s[i]
  ensures forall i :: 0 <= i < |s| ==> min_seq(s) <= s[i]
{
  if |s| == 1 then s[0]
  else if s[0] <= min_seq(s[1..]) then s[0]
  else min_seq(s[1..])
}

function max_seq(s: seq<real>): real
  requires |s| > 0
  ensures exists i :: 0 <= i < |s| && max_seq(s) == s[i]
  ensures forall i :: 0 <= i < |s| ==> s[i] <= max_seq(s)
{
  if |s| == 1 then s[0]
  else if s[0] >= max_seq(s[1..]) then s[0]
  else max_seq(s[1..])
}

/* helper modified by LLM (iteration 5): added lemma to prove affine transformation bounds */
lemma affine_bounds_lemma(x: real, min_val: real, max_val: real, shift: real, scale: real)
  requires scale > 0.0
  requires shift == -min_val
  requires scale == max_val - min_val
  requires min_val <= x <= max_val
  ensures 0.0 <= affine(x, shift, scale) <= 1.0
  ensures x == min_val ==> affine(x, shift, scale) == 0.0
  ensures x == max_val ==> affine(x, shift, scale) == 1.0
{
}

/* helper modified by LLM (iteration 5): lemma to establish affine equivalence from loop */
lemma affine_equivalence_lemma(s: seq<real>, r: seq<real>, shift: real, scale: real, idx: int)
  requires scale > 0.0
  requires 0 <= idx < |s| == |r|
  requires r[idx] == affine(s[idx], shift, scale)
  ensures r[idx] == (s[idx] + shift) / scale
{
}
// </vc-helpers>

// <vc-spec>
method rescale_to_unit(s: seq<real>) returns (r : seq<real>)

  requires |s| >= 2
  requires exists i, j : int :: (0 <= i < j < |s|) && s[i] != s[j]

  ensures |r| == |s|
  ensures forall i : int :: 0 <= i < |s| ==> 0.0 <= r[i] <= 1.0
  ensures exists i : int :: 0 <= i < |s| && r[i] == 0.0
  ensures exists i : int :: 0 <= i < |s| && r[i] == 1.0
  ensures exists shift, scale :: scale > 0.0 && affine_seq(s, r, shift, scale)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): added lemma calls to prove assertions */
  var min_val := min_seq(s);
  var max_val := max_seq(s);
  
  var shift := -min_val;
  var scale := max_val - min_val;
  
  assert scale > 0.0;
  
  r := [];
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant |r| == i
    invariant forall j :: 0 <= j < i ==> r[j] == affine(s[j], shift, scale)
    invariant forall j :: 0 <= j < i ==> 0.0 <= r[j] <= 1.0
  {
    affine_bounds_lemma(s[i], min_val, max_val, shift, scale);
    var new_val := affine(s[i], shift, scale);
    r := r + [new_val];
    i := i + 1;
  }
  
  assert affine_seq(s, r, shift, scale);
  
  var min_idx :| 0 <= min_idx < |s| && s[min_idx] == min_seq(s);
  var max_idx :| 0 <= max_idx < |s| && s[max_idx] == max_seq(s);
  
  affine_equivalence_lemma(s, r, shift, scale, min_idx);
  affine_bounds_lemma(s[min_idx], min_val, max_val, shift, scale);
  assert r[min_idx] == 0.0;
  
  affine_equivalence_lemma(s, r, shift, scale, max_idx);
  affine_bounds_lemma(s[max_idx], min_val, max_val, shift, scale);
  assert r[max_idx] == 1.0;
}
// </vc-code>
