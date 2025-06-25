// APELLIDOS: Heusel
// NOMBRE: Benedikt
// ESPECIALIDAD: ninguna (Erasmus)

// ESTÁ PERFECTO, NO HAY NINGUN COMENTARIO MAS ABAJO

// EJERCICIO 1 
// Demostrar el lemma div10_Lemma por inducción en n 
// y luego usarlo para demostrar el lemma div10Forall_Lemma

// ATOM 
// APELLIDOS: Heusel
// NOMBRE: Benedikt
// ESPECIALIDAD: ninguna (Erasmus)

// ESTÁ PERFECTO, NO HAY NINGUN COMENTARIO MAS ABAJO

// EJERCICIO 1 
// Demostrar el lemma div10_Lemma por inducción en n 
// y luego usarlo para demostrar el lemma div10Forall_Lemma

pub fn exp(x: int, e: nat) -> int
{
}

// ATOM 

pub fn div10_Lemma(n: nat)
    requires(n >= 3)
    ensures((exp(3, 4*n) + 9) % 10 == 0)
{
}

//Por inducción en n

// ATOM 
//Por inducción en n

pub fn div10Forall_Lemma()
    ensures(forall |n: int| n >= 3 ==> (exp(3, 4*n) + 9) % 10 == 0)
{
}

//Llamando al lemma anterior

// EJERCICIO 2
// Demostrar por inducción en n el lemma de abajo acerca de la función sumSerie que se define primero.
// Recuerda que debes JUSTIFICAR como se obtiene la propiedad del ensures a partir de la hipótesis de inducción.

// ATOM 
//Llamando al lemma anterior

// EJERCICIO 2
// Demostrar por inducción en n el lemma de abajo acerca de la función sumSerie que se define primero.
// Recuerda que debes JUSTIFICAR como se obtiene la propiedad del ensures a partir de la hipótesis de inducción.

pub fn sumSerie(x: int, n: nat) -> int
{
}

pub fn sumSerie_Lemma(x: int, n: nat)
    ensures((1 - x) * sumSerie(x, n) == 1 - exp(x, n + 1))
{
}

// EJERCICIO 3 
// Probar el lemma noSq_Lemma por contradicción + casos (ver el esquema de abajo).
// Se niega la propiedad en el ensures y luego se hacen dos casos (1) z%2 == 0 y (2) z%2 == 1.
// En cada uno de los dos casos hay que llegar a probar "assert false"

// ATOM 

// EJERCICIO 3 
// Probar el lemma noSq_Lemma por contradicción + casos (ver el esquema de abajo).
// Se niega la propiedad en el ensures y luego se hacen dos casos (1) z%2 == 0 y (2) z%2 == 1.
// En cada uno de los dos casos hay que llegar a probar "assert false"

pub fn notSq_Lemma(n: int)
    ensures(!(exists |z: int| z*z == 4*n + 2))
{
}

// EJERCICIO 4
//Probar el lemma oneIsEven_Lemma por contradicción, usando también el lemma del EJERCICIO 3.

// ATOM 

// EJERCICIO 4
//Probar el lemma oneIsEven_Lemma por contradicción, usando también el lemma del EJERCICIO 3.

pub fn oneIsEven_Lemma(x: int, y: int, z: int)
    requires(z*z == x*x + y*y)
    ensures(x % 2 == 0 || y % 2 == 0)
{
}

// Por contradicción, y usando notSq_Lemma.

//////////////////////////////////////////////////////////////////////////////////////////////

/* ESTE EJERCICIO SÓLO DEBES HACERLO SI HAS CONSEGUIDO DEMOSTRAR CON EXITO LOS EJERCICIOS 1 y 2

EJERCICIO 5 
En este ejercicio se dan dos lemma: exp_Lemma y prod_Lemma, que Dafny demuestra automáticamente.
Lo que se pide es probar expPlus1_Lemma, por inducción en n, haciendo una calculation con == y >=,
que en las pistas (hints) use la HI y también llamadas a esos dos lemas.
*/

// Por contradicción, y usando notSq_Lemma.

//////////////////////////////////////////////////////////////////////////////////////////////

/* ESTE EJERCICIO SÓLO DEBES HACERLO SI HAS CONSEGUIDO DEMOSTRAR CON EXITO LOS EJERCICIOS 1 y 2

EJERCICIO 5 
En este ejercicio se dan dos lemma: exp_Lemma y prod_Lemma, que Dafny demuestra automáticamente.
Lo que se pide es probar expPlus1_Lemma, por inducción en n, haciendo una calculation con == y >=,
que en las pistas (hints) use la HI y también llamadas a esos dos lemas.
*/
// ATOM 
pub fn exp_Lemma(x: int, e: nat)
    requires(x >= 1)
    ensures(exp(x, e) >= 1)
{
} //NO DEMOSTRAR, USAR PARA PROBAR EL DE ABAJO
 //NO DEMOSTRAR, USAR PARA PROBAR EL DE ABAJO

// ATOM 

pub fn prod_Lemma(z: int, a: int, b: int)
    requires(z >= 1 && a >= b >= 1)
    ensures(z*a >= z*b)
{
} //NO DEMOSTRAR, USAR PARA PROBAR EL DE ABAJO
 //NO DEMOSTRAR, USAR PARA PROBAR EL DE ABAJO

// ATOM 

pub fn expPlus1_Lemma(x: int, n: nat)
    requires(x >= 1 && n >= 1)
    ensures(exp(x + 1, n) >= exp(x, n) + 1)
{
}

// Por inducción en n, y usando exp_Lemma y prod_Lemma.

// Por inducción en n, y usando exp_Lemma y prod_Lemma.