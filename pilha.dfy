// integrantes: 

class Pilha { // sem autocontracts pra definir na mao os pre, pos, variantes e invariantes
    // ghost = abstrata
    ghost var Contents: seq<int>

    // concretos para fins de validação
    var elementos: array<int>
    var qntd: int

    ghost predicate Valid() 
        reads this, elementos
    {
        Contents is seq<int> && // verifica se Contents é uma sequência de inteiros
        qntd == |Contents| && // verifica se qntd é igual ao tamanho de Contents
        0 <= qntd <= elementos.Length && // verifica se qntd está dentro dos limites do array elementos (se ta igual ao length, tem que aumentar o valor)
        elementos.Length > 0 && // garante que o array elementos tem tamanho positivo
        Contents == elementos[0..qntd]  // verifica se Contents é igual a elementos até qntd
    }

    constructor() 
        ensures Valid()
        ensures Contents == []
        ensures qntd == 0 
    {
        elementos := new int[10];
        qntd := 0;
        Contents := [];
    }

    method push(x: int) 
        modifies this, elementos
        
        requires Valid()

        ensures Valid()
        ensures Contents == old(Contents) + [x]
        ensures qntd == old(qntd) + 1
        ensures elementos[0..qntd] == old(elementos[0..qntd]) + [x]
    {
        assert qntd <= elementos.Length;
        if qntd == elementos.Length {
            var novosElementos := new int[elementos.Length * 2];
            assert novosElementos.Length == 2 * elementos.Length;
            if qntd > 0 { // se tem mais de um elemento, copia os existentes pro novo array
                forall i | 0 <= i < elementos.Length {
                    novosElementos[i] := elementos[i];
                }
            }
            elementos := novosElementos; // passa pro array dos elementos
        }
        assert qntd < elementos.Length; 
        elementos[qntd] := x;
        qntd := qntd + 1;
        Contents := Contents + [x]; // atualizacao do ghost
    }

    method isEmpty() returns (b: bool) 
        requires Valid()
        ensures b <==> (qntd == 0)
        ensures Valid()
    {
        b := (qntd == 0);
    }
     
    method howManyStored() returns (n: int)
        requires Valid()
        ensures n == qntd
        ensures Valid()
    {
        n := qntd;
    }

    method pop() returns (x: int)
        requires Valid()
        requires qntd > 0 // garante que a pilha não está vazia
        // deveria ser isempty aqui como predicate?

        modifies this
        
        ensures Valid()
        ensures qntd == old(qntd) - 1 // garante que a quantidade de elementos diminuiu em 1
        ensures elementos.Length == old(elementos.Length) // o tamanho do array de elementos não muda
        ensures x == old(Contents)[|old(Contents)|-1] // garante que x é o último elemento de Contents
        ensures Contents == old(Contents)[0..|old(Contents)|-1] // remove o último elemento de Contents
    {
        x := elementos[qntd - 1]; // pega o último elemento
        qntd := qntd - 1; // diminui a quantidade de elementos
        Contents := Contents[0..|Contents|-1]; // remove o último elemento de Contents
    }


    method peek() returns (x: int)
        requires Valid()
        requires qntd > 0 // garante que a pilha não está vazia

        ensures Valid()
        ensures x == old(Contents)[|old(Contents)|-1] // garante que x é o último elemento de Contents
        ensures Contents == old(Contents) // Contents não muda, só x é atualizado
        ensures qntd == old(qntd) // a quantidade de elementos não muda
        ensures elementos.Length == old(elementos.Length) // o tamanho do array de elementos não muda
    {
        x := elementos[qntd - 1]; // pega o último elemento
        // não há necessidade de atualizar Contents, pois só estamos lendo o último elemento
    }   

    method reverse() {}

    method empilharDuas() {}
}