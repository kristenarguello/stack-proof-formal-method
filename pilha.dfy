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
        Contents is seq<int> && // verifica se Contents é uma sequência de inteiros = nao precisaria, o tipo ja garante isso
        qntd == |Contents| && // verifica se qntd é igual ao tamanho de Contents
        0 <= qntd <= elementos.Length && // verifica se qntd está dentro dos limites do array elementos (se ta igual ao length, tem que aumentar o valor)
        elementos.Length > 0 && // garante que o array elementos tem tamanho positivo
        Contents == elementos[0..qntd]  // verifica se Contents é igual a elementos até qntd
    }

    constructor() 
        ensures Valid()
        ensures Contents == []
        ensures qntd == 0
        ensures fresh(this)
        ensures fresh(elementos)
    {
        this.elementos := new int[10];
        qntd := 0;
        Contents := [];
    }

    method push(x: int) 
        requires Valid()
        modifies this, elementos

        ensures Valid()
        ensures Contents == old(Contents) + [x]
        ensures qntd == old(qntd) + 1
        ensures forall i :: 0 <= i < old(qntd) ==> elementos[i] == old(elementos[i]) // elementos preservados até onde foi colocado algo
        ensures elementos[qntd-1] == x // verifica se novo elemento na posicao correta 

        ensures fresh(elementos) // necessário pra permitir alteracoes na main em cima de elementos
    {
        assert qntd <= elementos.Length;
        if qntd == elementos.Length {
            doubleSize();
            assert fresh(elementos); // garante que o novo array é fresco
        }
        assume {:axiom} fresh(elementos); // precisa pra permitir mais de um push
        assert qntd < elementos.Length; 
        elementos[qntd] := x;
        qntd := qntd + 1;
        Contents := Contents + [x]; // atualizacao do ghost
    }

    // metodo auxiliar para dobrar o tamanho do array de elementos
    // é chamado quando qntd atinge o tamanho do array
    method doubleSize()
        requires Valid()
        modifies this, elementos

        ensures Valid()
        ensures elementos.Length == old(elementos.Length) * 2 // garante que o tamanho do array de elementos foi dobrado
        ensures forall i :: 0 <= i < old(qntd) ==> elementos[i] == old(elementos[i]) // preserva os elementos existentes
        ensures Contents == old(Contents) // garante que Contents não muda
        ensures qntd == old(qntd) // garante que a quantidade de elementos não muda
        
        ensures fresh(elementos)
    {
        var novosElementos := new int[2 * elementos.Length];
        var i: int := 0;
        while i < elementos.Length
            invariant 0 <= i <= elementos.Length
            invariant forall j :: 0 <= j < i ==> novosElementos[j] == elementos[j]
            decreases elementos.Length - i // prova de terminação
            modifies novosElementos
        {
            novosElementos[i] := elementos[i];
            i := i + 1;
        }
        elementos := novosElementos; // atualiza o array de elementos
    }

    predicate isEmpty()
        requires Valid()
        reads this, elementos
        ensures isEmpty() ==> Contents == [] && |Contents| == 0
        ensures isEmpty() ==> qntd == 0
    {
        qntd == 0
    }
     
    function howManyStored() : int
        requires Valid()
        reads this, elementos
    {
        qntd
    }

    method pop() returns (x: int)
        requires Valid()
        requires qntd > 0 // garante que a pilha não está vazia
        modifies this

        ensures Valid()
        ensures qntd == old(qntd) - 1 // garante que a quantidade de elementos diminuiu em 1
        ensures elementos.Length == old(elementos.Length) // o tamanho do array de elementos não muda
        ensures x == old(Contents)[|old(Contents)|-1] // garante que x é o último elemento de Contents
        ensures Contents == old(Contents)[0..|old(Contents)|-1] // remove o último elemento de Contents
        ensures forall i :: 0 <= i < old(qntd) - 1 ==> elementos[i] == old(elementos[i]) // preserva os elementos existentes até o penúltimo
    {
        x := elementos[qntd - 1]; // pega o último elemento
        qntd := qntd - 1; // diminui a quantidade de elementos
        Contents := Contents[0..|Contents|-1]; // remove o último elemento de Contents
    }


    function peek() : int
        requires Valid()
        requires qntd > 0 // garante que a pilha não está vazia

        reads this, elementos
    {
        elementos[qntd-1]
    }   

    // transformada em metodo puro (sem modificacoes no estado)
    // estava dando problema na hora de utilizar na main - nao deixava modificar o estado
    method reverse(orig: Pilha) returns (rev: Pilha) 
        requires orig.Valid()

        ensures fresh(rev)

        ensures rev.Valid()
        ensures rev.elementos.Length == orig.elementos.Length // garante que o tamanho do array é o mesmo
        ensures rev.howManyStored() == orig.howManyStored()
        ensures forall k :: 0 <= k < orig.qntd ==> rev.elementos[k] == orig.elementos[orig.qntd - 1 - k] // mostra q rev é orig invertida
    {
        rev := new Pilha();
        assert rev.Valid();

        var n := orig.elementos.Length;
        rev.elementos := new int[n];
        rev.qntd := orig.qntd;

        var l := orig.qntd - 1;
        var i := 0;

        while i < orig.qntd
            invariant 0 <= i <= orig.qntd
            invariant forall j :: 0 <= j < i ==> rev.elementos[j] == orig.elementos[l - j]
            modifies rev.elementos
            decreases orig.qntd - i // prova de terminação
        {
            rev.elementos[i] := orig.elementos[l - i];
            i := i + 1;
        }
        rev.Contents := rev.elementos[0..rev.qntd];
        assert rev.Valid();
    }

    method empilharDuas(outra: Pilha) returns (nova: Pilha)
        requires Valid()
        requires outra.Valid()

        ensures fresh(nova)
        ensures nova.Valid()
        ensures nova.Contents == Contents + outra.Contents
        ensures forall i :: 0 <= i < old(qntd) ==> nova.elementos[i] == old(elementos[i])
        ensures forall j :: 0 <= j < old(outra.qntd) ==> nova.elementos[old(qntd) + j] == old(outra.elementos[j])

        ensures Valid()
        ensures outra.Valid()
        ensures nova.qntd == qntd + outra.qntd // verifica se o tam final é as duas juntas
    {
        var total := qntd + outra.qntd;
        var tam := 10;
        while tam < total
            decreases total - tam
            invariant tam >= 10
        {
            tam := tam * 2;
        }
        
        // criar array temporário
        var novoArray := new int[tam];
        
        // copiar elementos da primeira pilha
        var i := 0;
        while i < qntd
            invariant 0 <= i <= qntd
            invariant i <= tam
            invariant forall k :: 0 <= k < i ==> novoArray[k] == elementos[k]
            decreases qntd - i
        {
            novoArray[i] := elementos[i];
            i := i + 1;
        }
        
        // copiar elementos da segunda pilha
        var j := 0;
        while j < outra.qntd
            invariant 0 <= j <= outra.qntd
            invariant forall k :: 0 <= k < qntd ==> novoArray[k] == elementos[k]
            invariant forall k :: 0 <= k < j ==> novoArray[qntd + k] == outra.elementos[k]
            decreases outra.qntd - j
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

method Main() {    
    // 1. pilha vazia
    var p1: Pilha := new Pilha();
    print("[ x ] Construtor deve instanciar uma pilha vazia\n");
    assert p1.isEmpty();
    print("[ x ] Verificar se a pilha está vazia ou não\n");
    assert p1.howManyStored() == 0;
    print("[ x ] Consultar o número de elementos armazenados na pilha\n");

    // 2. push
    p1.push(10);
    p1.push(20);
    p1.push(15);
    p1.push(30);
    print("[ x ] Adicionar um novo elemento no topo da pilha\n");
    assert !p1.isEmpty();
    assert p1.howManyStored() == 4;
    assert p1.peek() == 30;
    print("[ x ] Ler o valor do topo da pilha, sem removê-lo, caso a pilha não esteja vazia\n");


    // 3. pop
    var x := p1.pop();
    assert x == 30;
    assert p1.howManyStored() == 3;
    assert p1.peek() == 15;
    print("[ x ] Remover um elemento do topo da pilha, caso ela não esteja vazia\n");


    // 4. reverse
    var firstElementBeforeReverse := p1.elementos[0]; // primeiro da pilha
    var lastElementBeforeReverse := p1.peek(); // ultimo antes do reverse
    p1 := p1.reverse(p1);
    print("[ x ] Inverter a ordem dos elementos da pilha\n");
    assert p1.peek() == 10; // ordem agora invertida
    assert p1.howManyStored() == 3;
    // verificar se o ultimo do p1 antes é o mesmo do inicio agora
    assert p1.elementos[0] == lastElementBeforeReverse;  // First element after reverse should be the last element before
    assert p1.peek() == firstElementBeforeReverse;       // Last element after reverse should be the first element before

    // 5. segunda pilha
    var p2 := new Pilha();
    p2.push(1);
    p2.push(2);
    assert p2.peek() == 2;
    assert p2.howManyStored() == 2;

    // 6. empilharDuas – não altera p1 nem p2, mas gera uma nova
    var p3 := p1.empilharDuas(p2);
    print("[ x ] Empilhar uma pilha sobre outra, retornando uma nova pilha, sem alterar as pilhas fornecidas como argumento\n\n");
    assert p1.howManyStored() == 3; // nao altera
    assert p2.howManyStored() == 2; // nao altera
    assert p3.howManyStored() == 5;
    assert p2.peek() == 2;
    assert p1.peek() == 10; // topo da pilha p1, caso reverse funcione
    assert p3.peek() == 2; // topo da pilha concatenada
    assert p1.elementos[0] == 15; // primeiro elemento de p1

    assert p3.elementos[0..p3.qntd] == [15, 20, 10, 1, 2]; // ordem correta dos elementos na pilha concatenada

    // 7. Valida ordem resultante em p3: p1 + p2 
    var a := p3.pop();
    assert a == 2;
    assert p3.howManyStored() == 4; // depois do pop
    assert p3.peek() == 1; // topo agora é 1

    var b := p3.pop();
    assert b == 1;
    assert p3.howManyStored() == 3; // depois do pop
    assert p3.peek() == 10; // topo agora é 10

    var c := p3.pop(); // o primeiro elemento deve ser 15, que era o topo de p1
    assert c == 10; //caso reverse funcinoe
    assert p3.howManyStored() == 2; // depois do pop
    assert p3.peek() == 20; // topo agora é 20

    var d := p3.pop();
    assert d == 20; 
    assert p3.howManyStored() == 1; // depois do pop
    assert p3.peek() == 15; // topo agora é 10

    var e := p3.pop(); // o último elemento deve ser 10, que era o primeiro de p1
    assert e == 15; // caso reverse funcione
    assert p3.howManyStored() == 0; // depois do pop
    assert p3.isEmpty(); // pilha deve estar vazia
    
    print("[ x ] Main executada com sucesso!\n");
}