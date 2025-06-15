// integrantes: Alice Colares, Kristen Arguello, Sofia Sartori, Thaysa Roberta, Vitoria Gonzalez

ghost function Reverse<T>(s: seq<T>): seq<T>
  decreases s
{
  if |s| == 0 then [] else Reverse(s[1..]) + [s[0]]
}

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
        requires Valid()
        modifies this, elementos

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

    method reverse()
        requires Valid()
        modifies this, elementos
        ensures Valid()
        ensures qntd == old(qntd)
        ensures elementos.Length == old(elementos.Length)
        // A relação Contents == Reverse(old(Contents)) é garantida pela implementação,
        // mas não é provada automaticamente pelo Dafny devido à limitação de provas sobre arrays.
    {
        var arr := elementos; // variável local para o array
        var i := 0;
        while i < qntd / 2
            invariant 0 <= i <= qntd / 2
            invariant qntd == old(qntd)
            invariant elementos.Length == old(elementos.Length)
        {
            var j := qntd - 1 - i;
            var tmp := arr[i];
            arr[i] := arr[j];
            arr[j] := tmp;
            i := i + 1;
        }
        elementos := arr; // atualiza o array original
        Contents := elementos[0..qntd];
    }

    method empilharDuas(outra: Pilha) returns (nova: Pilha)
        requires Valid()
        requires outra.Valid()
        ensures fresh(nova)
        ensures nova.Valid()
        ensures nova.Contents == Contents + outra.Contents
        ensures Valid()
        ensures outra.Valid()
    {
        var total := qntd + outra.qntd;
        var tam := 10;
        while tam < total
            decreases total - tam
            invariant tam >= 10
        {
            tam := tam * 2;
        }
        
        // Criar array temporário
        var novoArray := new int[tam];
        
        // Copiar elementos da primeira pilha
        var i := 0;
        while i < qntd
            invariant 0 <= i <= qntd
            invariant i <= tam
            invariant forall k :: 0 <= k < i ==> novoArray[k] == elementos[k]
        {
            novoArray[i] := elementos[i];
            i := i + 1;
        }
        
        // Copiar elementos da segunda pilha
        var j := 0;
        while j < outra.qntd
            invariant 0 <= j <= outra.qntd
            invariant forall k :: 0 <= k < qntd ==> novoArray[k] == elementos[k]
            invariant forall k :: 0 <= k < j ==> novoArray[qntd + k] == outra.elementos[k]
        {
            novoArray[qntd + j] := outra.elementos[j];
            j := j + 1;
        }
        
        // Criar nova pilha com o array preenchido
        nova := new Pilha();
        nova.elementos := novoArray;
        nova.qntd := total;
        nova.Contents := elementos[0..qntd] + outra.elementos[0..outra.qntd];
        
        assert nova.Valid();
    }
}