```if-not:sql
Create a function (or write a script in Shell) that takes an integer as an argument and returns "Even" for even numbers or "Odd" for odd numbers.
```

```if:sql
## SQL Notes:
You will be given a table, `numbers`, with one column `number`.

Return a table with a column `is_even` containing "Even" or "Odd" depending on `number` column values.

### numbers table schema
* number INT

### output table schema
* is_even STRING
```

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded
