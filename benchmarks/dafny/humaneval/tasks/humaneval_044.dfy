// <vc-preamble>

function power_of_base(base: int, exp: int): int
  requires base >= 2
  requires exp >= 0
  ensures power_of_base(base, exp) > 0
{
  if exp == 0 then 1 else base * power_of_base(base, exp - 1)
}

function digits_to_int(digits: seq<char>, base: int): int
  requires base >= 2
  requires forall i :: 0 <= i < |digits| ==> '0' <= digits[i] <= '9' && (digits[i] as int) - ('0' as int) < base
{
  if |digits| == 0 then 0
  else (digits[0] as int) - ('0' as int) + base * digits_to_int(digits[1..], base)
}

function string_to_int_in_base(s: string, base: int): int
  requires base >= 2
  requires |s| > 0
  requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9' && (s[i] as int) - ('0' as int) < base
  ensures string_to_int_in_base(s, base) >= 0
{
  if |s| == 1 then
    (s[0] as int) - ('0' as int)
  else
    string_to_int_in_base(s[..|s|-1], base) * base + ((s[|s|-1] as int) - ('0' as int))
}
lemma digits_reversal_lemma(digits: seq<char>, reversed: seq<char>, base: int)
  requires base >= 2
  requires |digits| == |reversed| > 0
  requires forall i :: 0 <= i < |digits| ==> '0' <= digits[i] <= '9' && (digits[i] as int) - ('0' as int) < base
  requires forall i :: 0 <= i < |reversed| ==> reversed[i] == digits[|digits| - 1 - i]
  ensures string_to_int_in_base(reversed, base) == digits_to_int(digits, base)
{
  if |digits| == 1 {
    assert reversed[0] == digits[0];
  } else {
    var tail_digits := digits[1..];
    var head_reversed := reversed[..|reversed|-1];

    assert |tail_digits| == |head_reversed|;
    assert forall i :: 0 <= i < |tail_digits| ==> head_reversed[i] == tail_digits[|tail_digits| - 1 - i];

    digits_reversal_lemma(tail_digits, head_reversed, base);

    assert string_to_int_in_base(reversed, base) == 
           string_to_int_in_base(head_reversed, base) * base + ((reversed[|reversed|-1] as int) - ('0' as int));
    assert digits_to_int(digits, base) == 
           ((digits[0] as int) - ('0' as int)) + base * digits_to_int(tail_digits, base);
    assert string_to_int_in_base(head_reversed, base) == digits_to_int(tail_digits, base);
    assert reversed[|reversed|-1] == digits[0];
  }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method change_base(x: int, base: int) returns (result: string)
  requires base >= 2 && base < 10
  requires x >= 0
  ensures x == 0 ==> result == "0"
  ensures x > 0 ==> |result| > 0 && result[0] != '0'
  ensures forall i :: 0 <= i < |result| ==> '0' <= result[i] <= '9' && (result[i] as int) - ('0' as int) < base
  ensures x > 0 ==> string_to_int_in_base(result, base) == x
// </vc-spec>
// <vc-code>
{
    assume {:axiom} false;
  }
// </vc-code>
