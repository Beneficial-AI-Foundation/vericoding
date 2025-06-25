//This method should return true iff pre is a prefix of str. That is, str starts with pre
// SPEC 
//This method should return true iff pre is a prefix of str. That is, str starts with pre
pub fn isPrefix(pre: &str, str: &str) -> bool
    requires(0 < pre.len() <= str.len()) //This line states that this method requires that pre is less than or equal in length to str. Without this line, an out of bounds error is shown on line 14: "str[i] != pre[i]"
{
}