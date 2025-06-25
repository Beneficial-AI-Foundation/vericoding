pub fn longest_common_prefix(str1: Seq<char>, str2: Seq<char>) -> (prefix: Seq<char>)
    ensures(|prefix| <= |str1| && prefix == str1.subrange(0, |prefix| as int) && |prefix| <= |str2| && prefix == str2.subrange(0, |prefix| as int))
    ensures(|prefix| == |str1| || |prefix| == |str2| || (str1[|prefix| as int] != str2[|prefix| as int]))
{
}