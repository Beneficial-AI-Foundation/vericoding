/-
When you were little, your mother used to make the most delicious cookies, which you could not resist. So, every now and then, when your mother didn't see you, you sneaked into the kitchen, climbed onto a stool to reach the cookie jar, and stole a cookie or two. However, sometimes while doing this, you would hear foot steps approaching, so you quickly jumped down from the stool and, when your mother entered the kitchen, you pretended as if nothing had happened (whistle, whistle innocently). However, your mother knew. How did she know? You forgot to put the lid back on the cookie jar! Oh, no!

Growing older (and still not able to resist your mother's cookies), you deviced a contraption that would automatically put the lid back on the cookie jar, _no matter what would happen_.

The class `CookieJar` is provided: 
```Python
class CookieJar(object):

    def __init__(self):
        self._is_open = False

    def take(self):
        if not self._is_open:
            raise ValueError("Cookie jar is closed")
        return "Cookie"

    def open_jar(self):
        self._is_open = True

    def close_jar(self):
        self._is_open = False

    def is_open(self):
        return self._is_open
```
Your task is to implement the 'contraption' `SelfClosing` (class, method, whatever; it's your choice) such that, given an instance`cookie_jar` of `CookieJar`, you may call:

```Python
with SelfClosing(cookie_jar) as jar:
    cookie = jar.take()
```
after which, `cookie_jar.is_open() == False`, _no matter what_.

Do not alter the provided code. (Tests will be performed with a code that differs slightly from the one provided, so modifying it is to no avail.)

Enjoy!
-/

def CookieJar.is_open : CookieJar → Bool 
  | _ => sorry

-- <vc-helpers>
-- </vc-helpers>

def CookieJar.take (jar : CookieJar) : String :=
  sorry

structure SelfClosing (jar : CookieJar) where
  mk ::

theorem cookie_jar_initial_state (jar : CookieJar) : 
  jar.is_open = false := sorry 

theorem context_manager_always_closes (jar : CookieJar) (e : Exception) :
  ¬jar.is_open := sorry

theorem nested_context_managers (jar : CookieJar) 
  (ctx1 ctx2 : SelfClosing jar) :
  jar.is_open ∧
  (jar.is_open ∧ ¬jar.is_open) ∧
  ¬jar.is_open := sorry

theorem multiple_operations {α : Type} (ops : List α) (jar : CookieJar) 
  (h : ops.length > 0) :
  ∀ op ∈ ops,
    jar.take = "Cookie" ∧ 
    jar.is_open ∧
    ¬jar.is_open := sorry

theorem nested_depth (n : Nat) (jar : CookieJar) (h : n > 0 ∧ n ≤ 100) :
  jar.is_open ∧
  jar.take = "Cookie" ∧ 
  jar.is_open ∧
  ¬jar.is_open := sorry

-- Apps difficulty: introductory
-- Assurance level: guarded