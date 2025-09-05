Given an absolute path for a file (Unix-style), simplify it.

For example,
path = "/home/", => "/home"
path = "/a/./b/../../c/", => "/c"

Corner Cases:

       Did you consider the case where path = "/../"?
       In this case, you should return "/".
       Another corner case is the path might contain multiple slashes '/' together, such as "/home//foo/".
       In this case, you should ignore redundant slashes and return "/home/foo".

def simplify_path (s : String) : String := sorry

def is_valid_path_segment (s : String) : Bool := sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded
