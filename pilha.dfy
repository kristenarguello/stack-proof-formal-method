// integrantes: 

class {:autocontracts} Pilha { // autocontracts para cobrir valid() antes e depois de cada operação
    // ghost = abstrata
    ghost var Contents: seq<int>

    // concretos para fins de validação
    var elementos: array<int>
    var qntd: int

    ghost predicate Valid() {
        Contents is seq<int> && // verifica se Contents é uma sequência de inteiros
        qntd == |Contents| && // verifica se qntd é igual ao tamanho de Contents
        0 <= qntd <= elementos.Length && // verifica se qntd está dentro dos limites do array
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

    method isEmpty() return (b: bool) 
        requires Valid()
        ensures b <==> (qntd == 0)
        ensures Valid()
    {
        b := (qntd == 0);
    }
}