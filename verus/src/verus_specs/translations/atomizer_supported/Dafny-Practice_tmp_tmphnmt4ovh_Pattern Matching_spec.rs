pub fn FindAllOccurrences(text: &str, pattern: &str) -> (offsets: std::collections::HashSet<usize>)
    requires(
        true
    )
    ensures(|offsets: std::collections::HashSet<usize>| 
        forall(|i: usize| offsets.contains(&i) ==> i + pattern.len() <= text.len()) &&
        forall(|i: usize| 0 <= i && i <= text.len() - pattern.len() ==> 
            (&text[i..i+pattern.len()] == pattern <==> offsets.contains(&i)))
    )
{
}

pub fn RecursiveSumDown(str: &str) -> (result: i32)
    requires(true)
    ensures(|result: i32| true)
{
}

pub fn RecursiveSumUp(str: &str) -> (result: i32)
    requires(true)
    ensures(|result: i32| true)
{
}

pub fn LemmaRabinKarp(t_sub: &str, pattern: &str, text_hash: i32, pattern_hash: i32)
    requires(
        text_hash != pattern_hash &&
        pattern_hash == RecursiveSumDown(pattern) &&
        text_hash == RecursiveSumDown(t_sub)
    )
    ensures(
        t_sub != pattern
    )
{
}

pub fn Lemma2Sides(text: &str, pattern: &str, i: usize, offsets: &std::collections::HashSet<usize>)
    requires(
        0 <= i && i <= text.len() - pattern.len() &&
        (&text[i..i+pattern.len()] == pattern ==> offsets.contains(&i)) &&
        (&text[i..i+pattern.len()] == pattern <== offsets.contains(&i))
    )
    ensures(
        &text[i..i+pattern.len()] == pattern <==> offsets.contains(&i)
    )
{
}

pub fn LemmaHashEqualty(text_hash: i32, text: &str, i: usize, old_text_hash: i32, pattern: &str)
    requires(
        0 < i && i <= text.len() - pattern.len() &&
        text_hash == old_text_hash - text.chars().nth(i - 1).unwrap() as i32 + text.chars().nth(i - 1 + pattern.len()).unwrap() as i32 &&
        old_text_hash == RecursiveSumDown(&text[i - 1..i - 1 + pattern.len()])
    )
    ensures(
        text_hash == RecursiveSumDown(&text[i..i+pattern.len()])
    )
{
}

pub fn LemmaAddingOneIndex(str: &str, i: usize, sum: i32)
    requires(
        0 <= i && i < str.len() && sum == RecursiveSumDown(&str[..i])
    )
    ensures(
        0 <= i+1 && i+1 <= str.len() && sum + str.chars().nth(i).unwrap() as i32 == RecursiveSumDown(&str[..i+1])
    )
{
}

pub fn PrependSumUp(str: &str)
    requires(
        str != ""
    )
    ensures(
        RecursiveSumUp(str) == str.chars().nth(0).unwrap() as i32 + RecursiveSumUp(&str[1..])
    )
{
}

pub fn EquivalentSumDefinitions(str: &str)
    requires(true)
    ensures(
        RecursiveSumDown(str) == RecursiveSumUp(str)
    )
{
}