```vc-helpers
function Int2Str(n: nat): string
  decreases n
{
  if n == 0 then "" else Int2Str(n / 2) + (if n % 2 == 1 then "1" else "0")
}

function method Parse(s: string): nat
  decreases s
{
  if |s| == 0 then 0 else 2 * Parse(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0)
}

lemma Parse_correct(s: string)
  ensures Parse(s) == Str2Int(s)
  decreases s
{
  if |s| == 0 {
  } else {
    Parse_correct(s[0..|s|-1]);
    assert Parse(s) == 2 * Parse(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0);
    assert Str2Int(s) == 2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0);
    assert Parse(s[0..|s|-1]) == Str2Int(s[0..|s|-1]);
  }
}

function method Exp_exec(x: nat, y: nat): nat
  decreases y
{
  if y == 0 then 1 else x * Exp_exec(x, y - 1)
}

lemma Exp_exec_correct(x: nat, y: nat)
  ensures Exp_exec(x, y) == Exp_int(x, y)
  decreases y
{
  if y == 0 {
  } else {
    Exp_exec_correct(x, y - 1);
    assert Exp_exec(x, y) == x * Exp_exec(x, y - 1);
    assert Exp_int(x, y) == x * Exp_int(x, y - 1);
  }
}

lemma Str2Int_append(s: string, b: string)
  requires |b| == 1
  requires b[0] == '0' || b[0] == '1'
  ensures Str2Int(s + b) == 2 * Str2Int(s) + (if b[0] == '1' then 1 else 0)
  decreases |s|
{
  assert Str2Int(s + b) ==
    (if |s + b| == 0 then 0 else 2 * Str2Int((s + b)[0..|s + b| - 1]) + (if (s + b)[|s + b| - 1] == '1' then 1 else 0));
  assert |s + b| > 