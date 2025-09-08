/-
This is another problem about Indraneel's library. His library has one long shelf. His books are numbered and he identifies the books by their number. Each book has a distinct number.
He has lost many books, since many of his friends borrow his books and never bother to return them. He does not want to lose any more books and has decided to keep a record of all books that he lends to his friends. To make the task of borrowing a book a little difficult, he has given the following instructions to his friends: when they borrow a book, they must record in a register its position from the left among the books currently on the shelf.
Suppose there are $5$ books in the library and they are arranged as follows:
261421532614215326 \quad 1 \quad 42 \quad 15 \quad 3
If someone walks in and borrows the book $42$, then he will record $3$ in the register because this book is the third from the left on the shelf. Now the shelf looks like this:
26115326115326 \quad 1 \quad 15 \quad 3
If the next person borrow the book $3$, he writes down $4$ in the register since this is currently the fourth book from the left on the shelf, and so on.
Indraneel knows the initial arrangement of the books in his library at the time that he introduced the register system. After a while he examines his register and would like to know which books have been borrowed. Your task is to write a program to help Indraneel solve this problem.

-----Input:-----
The first line of the input contains a single integer $M$ indicating the number of books in Indraneel's library. The next line contains $M$ distinct positive integers describing the sequence in which the books are arranged on the library shelf. The third line of input contains a single integer $N$ indicating the number of entries in the register. This, in turn, is followed by $N$ lines (lines $4$ to $N+3$), each containing one positive integer. The integer on line $3+i$ indicates the position from left of the book ith book borrowed. (You may assume that the number on line $3+i$ is at most $M-i+1$.)

-----Output:-----
$N$ lines with one positive integer on each line. The number on line $i$ is the book borrowed by the ith borrower.

-----Constraints:-----
- $1 \leq M \leq 1000000$.
- $1 \leq N \leq 4000$.

-----Sample Input-----
5
26 1 42 15 3 
2
3
4

-----Sample Output-----
42
3
-/

-- <vc-helpers>
-- </vc-helpers>

def find_borrowed_books (n : Nat) (books : List Nat) (k : Nat) (positions : List Nat) : List Nat :=
sorry

theorem find_borrowed_books_middle_and_end 
  (books : List Nat := [26, 1, 42, 15, 3])
  (n : Nat := 5)
  (k : Nat := 2) 
  (positions : List Nat := [3, 4]) :
  find_borrowed_books n books k positions = [42, 3] :=
sorry

theorem find_borrowed_books_start
  (books : List Nat := [1, 2, 3])
  (n : Nat := 3)
  (k : Nat := 2)
  (positions : List Nat := [2, 1]) :
  find_borrowed_books n books k positions = [2, 1] :=
sorry

theorem find_borrowed_books_single
  (books : List Nat := [10, 20, 30]) 
  (n : Nat := 3)
  (k : Nat := 1)
  (positions : List Nat := [2]) :
  find_borrowed_books n books k positions = [20] :=
sorry

theorem find_borrowed_books_length
  (n : Nat)
  (books : List Nat)
  (k : Nat)
  (positions : List Nat)
  (h1 : k = positions.length)
  (h2 : k ≤ n)
  (h3 : n = books.length) :
  (find_borrowed_books n books k positions).length = k :=
sorry

-- Apps difficulty: interview
-- Assurance level: guarded