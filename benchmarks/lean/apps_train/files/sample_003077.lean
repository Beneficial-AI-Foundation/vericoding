Hey CodeWarrior,

we've got a lot to code today!

I hope you know the basic string manipulation methods, because this kata will be all about them.

Here we go...

## Background

We've got a very long string, containing a bunch of User IDs. This string is a listing, which seperates each user ID with a comma and a whitespace ("' "). Sometimes there are more than only one whitespace. Keep this in mind! Futhermore, some user Ids are written only in lowercase, others are mixed lowercase and uppercase characters. Each user ID starts with the same 3 letter "uid", e.g. "uid345edj". But that's not all! Some stupid student edited the string and added some hashtags (#). User IDs containing hashtags are invalid, so these hashtags should be removed!

## Task

1.  Remove all hashtags
2.  Remove the leading "uid" from each user ID
3.  Return an array of strings --> split the string
4.  Each user ID should be written in only lowercase characters
5.  Remove leading and trailing whitespaces

---

## Note

Even if this kata can be solved by using Regex or Linq, please try to find a solution by using only C#'s string class.

Some references for C#:

- [Microsoft MDSN: Trim](https://msdn.microsoft.com/de-de/library/t97s7bs3%28v=vs.110%29.aspx)
- [Microsoft MSDN: Split](https://msdn.microsoft.com/de-de/library/tabh47cf%28v=vs.110%29.aspx)
- [Microsoft MSDN: ToLower](https://msdn.microsoft.com/en-us/library/system.string.tolower%28v=vs.110%29.aspx)
- [Microsoft MSDN: Replace](https://msdn.microsoft.com/de-de/library/fk49wtc1%28v=vs.110%29.aspx)
- [Microsoft MSDN: Substring](https://msdn.microsoft.com/de-de/library/aka44szs%28v=vs.110%29.aspx)

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded