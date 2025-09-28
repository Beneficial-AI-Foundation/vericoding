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
function reverse(s: seq<char>): seq<char> 
  ensures |reverse(s)| == |s|
  ensures forall i :: 0 <= i < |s| ==> reverse(s)[i] == s[|s| - 1 - i]
{
  if |s| == 0 then [] else reverse(s[1..]) + [s[0]]
}

predicate valid_base_char(c: char, base: int) 
  requires base >= 2
{ 
  '0' <= c <= '9' && (c as int) - ('0' as int) < base 
}

lemma zero_case_lemma(x: int, base: int)
  requires base >= 2 && x == 0
  ensures string_to_int_in_base("0", base) == x
{
}

lemma nonzero_digits_lemma(result: string, base: int)
  requires base >= 2
  requires |result| > 0 && result[0] != '0'
  requires forall i :: 0 <= i < |result| ==> valid_base_char(result[i], base)
  ensures string_to_int_in_base(result, base) > 0
{
  /* helper modified by LLM (iteration 5): Fixed lemma implementation */
  if |result| == 1 {
    assert (result[0] as int) - ('0' as int) > 0;
    assert string_to_int_in_base(result, base) == (result[0] as int) - ('0' as int);
  } else {
    var truncated := result[..|result|-1];
    nonzero_digits_lemma(truncated, base);
    assert string_to_int_in_base(result, base) == string_to_int_in_base(truncated, base) * base + ((result[|result|-1] as int) - ('0' as int));
  }
}

lemma power_of_base_positive(base: int, exp: int)
  requires base >= 2 && exp >= 0
  ensures power_of_base(base, exp) > 0
{
  if exp > 0 {
    power_of_base_positive(base, exp - 1);
  }
}

lemma division_lemma(n: int, base: int)
  requires base >= 2 && n >= 0
  ensures n % base >= 0 && n % base < base
  ensures n / base >= 0 && n / base <= n
{
}

function seq_to_string(chars: seq<char>): string
  ensures |seq_to_string(chars)| == |chars|
  ensures forall i :: 0 <= i < |chars| ==> seq_to_string(chars)[i] == chars[i]
{
  if |chars| == 0 then "" else
    [chars[0]] + seq_to_string(chars[1..])
}

lemma digits_building_lemma(n: int, base: int, digits: seq<char>)
  requires base >= 2 && n >= 0
  requires forall c :: c in digits ==> valid_base_char(c, base)
  requires n == n * power_of_base(base, |digits|) + digits_to_int(reverse(digits), base)
  ensures digits_to_int(reverse(digits), base) < power_of_base(base, |digits|)
{
}

lemma digit_conversion_lemma(remainder: int, base: int)
  requires base >= 2
  requires 0 <= remainder < base
  ensures '0' <= (remainder + '0' as int) as char <= '9'
  ensures ((remainder + '0' as int) as char as int) - ('0' as int) == remainder
{
}
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
  /* code modified by LLM (iteration 5): Fixed compilation error by removing undefined variable x */
  if x == 0 {
    result := "0";
    return;
  }
  
  var n := x;
  var digits: seq<char> := [];
  
  while n > 0
    invariant n >= 0
    invariant forall c :: c in digits ==> valid_base_char(c, base)
    invariant x == n * power_of_base(base, |digits|) + digits_to_int(reverse(digits), base)
    invariant |digits| > 0 ==> digits[0] != '0'
    invariant digits_to_int(reverse(digits), base) < power_of_base(base, |digits|)
    decreases n
  {
    var remainder := n % base;
    n := n / base;
    var digit_char: char := (remainder + '0' as int) as char;
    digits := [digit_char] + digits;
    
    if |digits| > 0 {
      assert digit_char != '0' || |digits| > 1;
    }
  }
  
  result := seq_to_string(digits);
  
  if x > 0 {
    nonzero_digits_lemma(result, base);
  }
}
// </vc-code>
