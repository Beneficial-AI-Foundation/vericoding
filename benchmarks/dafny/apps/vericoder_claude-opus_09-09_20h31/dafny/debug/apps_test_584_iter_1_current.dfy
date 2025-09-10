function IsLetter(c: char): bool
{
    ('a' <= c <= 'z') || ('A' <= c <= 'Z')
}

predicate ValidParentheses(input: string)
{
    var newlinePos := FindNewline(input);
    if newlinePos >= |input| then true
    else
        var s := if newlinePos + 1 < |input| then input[newlinePos + 1..] else "";
        IsValidParenthesesSequence(s, 0, 0)
}

predicate IsValidParenthesesSequence(s: string, pos: int, balance: int)
    requires 0 <= pos <= |s|
    requires balance >= 0
    decreases |s| - pos
{
    if pos >= |s| then balance == 0
    else
        var c := s[pos];
        var newBalance := if c == '(' then balance + 1 
                         else if c == ')' then balance - 1 
                         else balance;
        newBalance >= 0 && IsValidParenthesesSequence(s, pos + 1, newBalance)
}

function LongestWordOutside(input: string): int
{
    var newlinePos := FindNewline(input);
    if newlinePos >= |input| then 0
    else
        var s := if newlinePos + 1 < |input| then input[newlinePos + 1..] else "";
        ComputeLongestOutside(s, 0, 0, 0, 0)
}

function CountWordsInside(input: string): int
{
    var newlinePos := FindNewline(input);
    if newlinePos >= |input| then 0
    else
        var s := if newlinePos + 1 < |input| then input[newlinePos + 1..] else "";
        ComputeCountInside(s, 0, 0, 0)
}

predicate ValidOutput(input: string, len_out: int, count_in: int)
{
    len_out >= 0 && count_in >= 0 &&
    len_out == LongestWordOutside(input) &&
    count_in == CountWordsInside(input)
}

function FindNewline(input: string): int
    ensures 0 <= FindNewline(input) <= |input|
{
    FindNewlineHelper(input, 0)
}

function FindNewlineHelper(input: string, pos: int): int
    requires 0 <= pos <= |input|
    ensures pos <= FindNewlineHelper(input, pos) <= |input|
    decreases |input| - pos
{
    if pos >= |input| then pos
    else if input[pos] == '\n' then pos
    else FindNewlineHelper(input, pos + 1)
}

function ComputeLongestOutside(s: string, pos: int, balance: int, cur: int, best: int): int
    requires 0 <= pos <= |s|
    requires balance >= 0
    requires cur >= 0 && best >= 0
    ensures ComputeLongestOutside(s, pos, balance, cur, best) >= 0
    decreases |s| - pos
{
    if pos >= |s| then
        if cur > best && balance == 0 then cur else best
    else
        var c := s[pos];
        var newBalance := if c == '(' then balance + 1 
                         else if c == ')' then (if balance > 0 then balance - 1 else 0)
                         else balance;
        var newCur := if IsLetter(c) then cur + 1
                     else if cur > 0 then 0
                     else cur;
        var newBest := if !IsLetter(c) && cur > 0 && balance == 0 then
                          if cur > best then cur else best
                      else best;
        ComputeLongestOutside(s, pos + 1, newBalance, newCur, newBest)
}

function ComputeCountInside(s: string, pos: int, balance: int, cur: int): int
    requires 0 <= pos <= |s|
    requires balance >= 0
    requires cur >= 0
    ensures ComputeCountInside(s, pos, balance, cur) >= 0
    decreases |s| - pos
{
    if pos >= |s| then 0
    else
        var c := s[pos];
        var newBalance := if c == '(' then balance + 1 
                         else if c == ')' then (if balance > 0 then balance - 1 else 0)
                         else balance;
        var newCur := if IsLetter(c) then cur + 1
                     else if cur > 0 then 0
                     else cur;
        var wordEnded := !IsLetter(c) && cur > 0;
        var countIncrement := if wordEnded && balance > 0 then 1 else 0;
        countIncrement + ComputeCountInside(s, pos + 1, newBalance, newCur)
}

// <vc-helpers>
lemma ComputeLongestOutsideCorrect(s: string, pos: int, balance: int, cur: int, best: int)
    requires 0 <= pos <= |s|
    requires balance >= 0
    requires cur >= 0 && best >= 0
    ensures ComputeLongestOutside(s, pos, balance, cur, best) >= best
    decreases |s| - pos
{
    if pos >= |s| {
        // Base case is trivial
    } else {
        ComputeLongestOutsideCorrect(s, pos + 1, 
            if s[pos] == '(' then balance + 1 
            else if s[pos] == ')' then (if balance > 0 then balance - 1 else 0)
            else balance,
            if IsLetter(s[pos]) then cur + 1
            else if cur > 0 then 0
            else cur,
            if !IsLetter(s[pos]) && cur > 0 && balance == 0 then
                if cur > best then cur else best
            else best);
    }
}

lemma ComputeCountInsideCorrect(s: string, pos: int, balance: int, cur: int)
    requires 0 <= pos <= |s|
    requires balance >= 0
    requires cur >= 0
    ensures ComputeCountInside(s, pos, balance, cur) >= 0
    decreases |s| - pos
{
    // Follows from the ensures clause of ComputeCountInside
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: (int, int))
    requires |input| > 0
    requires exists i :: 0 <= i < |input| && input[i] == '\n'
    requires forall i :: 0 <= i < |input| ==> (IsLetter(input[i]) || input[i] == '_' || input[i] == '(' || input[i] == ')' || input[i] == '\n' || input[i] == '\r' || ('0' <= input[i] <= '9'))
    requires ValidParentheses(input)
    ensures result.0 >= 0 && result.1 >= 0
    ensures result.0 == LongestWordOutside(input)
    ensures result.1 == CountWordsInside(input)
    ensures ValidOutput(input, result.0, result.1)
// </vc-spec>
// <vc-code>
{
    var newlinePos := 0;
    while newlinePos < |input| && input[newlinePos] != '\n'
        invariant 0 <= newlinePos <= |input|
        invariant forall i :: 0 <= i < newlinePos ==> input[i] != '\n'
        invariant FindNewline(input) == FindNewlineHelper(input, newlinePos)
    {
        newlinePos := newlinePos + 1;
    }

    if newlinePos >= |input| {
        return (0, 0);
    }

    var s := if newlinePos + 1 < |input| then input[newlinePos + 1..] else "";
    
    var pos := 0;
    var balance := 0;
    var cur := 0;
    var best := 0;
    var count := 0;

    while pos < |s|
        invariant 0 <= pos <= |s|
        invariant balance >= 0
        invariant cur >= 0 && best >= 0
        invariant count >= 0
        invariant best == ComputeLongestOutside(s[0..pos], 0, 0, 0, 0)
        invariant count == ComputeCountInside(s[0..pos], 0, 0, 0)
        invariant ComputeLongestOutside(s, 0, 0, 0, 0) == 
                  ComputeLongestOutside(s[0..pos], 0, 0, 0, 0) + 
                  ComputeLongestOutside(s[pos..], 0, balance, cur, 0) - 
                  (if ComputeLongestOutside(s[pos..], 0, balance, cur, 0) > 0 then 0 else best)
        invariant ComputeCountInside(s, 0, 0, 0) == 
                  count + ComputeCountInside(s[pos..], 0, balance, cur)
    {
        var c := s[pos];
        
        var wordEnded := !IsLetter(c) && cur > 0;
        
        if wordEnded && balance == 0 {
            if cur > best {
                best := cur;
            }
        } else if wordEnded && balance > 0 {
            count := count + 1;
        }
        
        if c == '(' {
            balance := balance + 1;
        } else if c == ')' {
            if balance > 0 {
                balance := balance - 1;
            }
        }
        
        if IsLetter(c) {
            cur := cur + 1;
        } else if cur > 0 {
            cur := 0;
        }
        
        pos := pos + 1;
    }
    
    if cur > best && balance == 0 {
        best := cur;
    }
    
    return (best, count);
}
// </vc-code>

