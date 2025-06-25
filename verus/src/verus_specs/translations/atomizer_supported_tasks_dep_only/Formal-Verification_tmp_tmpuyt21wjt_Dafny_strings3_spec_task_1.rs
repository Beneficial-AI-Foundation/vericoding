use vstd::prelude::*;

verus! {

predicate isPrefixPred(pre: Seq<char>, str: Seq<char>) {
    (pre.len() <= str.len()) && 
    pre == str.subrange(0, pre.len() as int)
}

predicate isNotPrefixPred(pre: Seq<char>, str: Seq<char>) {
    (pre.len() > str.len()) || 
    pre != str.subrange(0, pre.len() as int)
}

pub fn isPrefix(pre: Seq<char>, str: Seq<char>) -> (res: bool)
    ensures
        !res <==> isNotPrefixPred(pre, str),
        res <==> isPrefixPred(pre, str)
{
}

}