// integrantes: Alice Colares, Kristen Arguello, Sofia Sartori, Thaysa Roberta, Vitoria Gonzalez

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
                var i := 0;
                while i < elementos.Length
                    invariant 0 <= i <= elementos.Length
                    invariant forall j | 0 <= j < i :: novosElementos[j] == elementos[j]
                    decreases elementos.Length - i
                {
                    novosElementos[i] := elementos[i];
                    i := i + 1;
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

    method reverse()
        requires Valid()
        modifies this
        ensures Valid()
        ensures Contents == reverse(old(Contents))
        ensures qntd == old(qntd)
        ensures elementos.Length == old(elementos.Length)
    {
        var i := 0;
        while i < qntd / 2
            invariant 0 <= i <= qntd / 2
            invariant forall j | 0 <= j < i :: elementos[j] == old(elementos)[qntd - 1 - j]
            invariant forall j | 0 <= j < i :: elementos[qntd - 1 - j] == old(elementos)[j]
            invariant forall j | i <= j < qntd - i :: elementos[j] == old(elementos)[j]
            decreases qntd / 2 - i
        {
            var temp := elementos[i];
            elementos[i] := elementos[qntd - 1 - i];
            elementos[qntd - 1 - i] := temp;
            i := i + 1;
        }
        Contents := reverse(Contents);
    }

    method empilharDuas(p1: Pilha, p2: Pilha) returns (resultado: Pilha)
        requires p1.Valid()
        requires p2.Valid()
        ensures resultado.Valid()
        ensures resultado.Contents == p1.Contents + p2.Contents
        ensures resultado.qntd == p1.qntd + p2.qntd
        ensures p1.Valid() && p1.Contents == old(p1.Contents)
        ensures p2.Valid() && p2.Contents == old(p2.Contents)
    {
        resultado := new Pilha();
        var i := 0;
        while i < p1.qntd
            invariant 0 <= i <= p1.qntd
            invariant resultado.Valid()
            invariant resultado.Contents == p1.Contents[0..i]
            invariant resultado.qntd == i
            decreases p1.qntd - i
        {
            resultado.push(p1.elementos[i]);
            i := i + 1;
        }
        
        i := 0;
        while i < p2.qntd
            invariant 0 <= i <= p2.qntd
            invariant resultado.Valid()
            invariant resultado.Contents == p1.Contents + p2.Contents[0..i]
            invariant resultado.qntd == p1.qntd + i
            decreases p2.qntd - i
        {
            resultado.push(p2.elementos[i]);
            i := i + 1;
        }
    }
}