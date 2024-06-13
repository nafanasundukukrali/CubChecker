:- use_module(library(pce)).
:- use_module(library(pce_main)).
:- use_module(library(dif)).	% Sound inequality
:- use_module(library(clpfd)).	% Finite domain constraints
:- use_module(library(clpb)).	% Boolean constraints
:- use_module(library(chr)).	% Constraint Handling Rules
:- use_module(library(when)).	% Coroutining
:- use_module(library(lists)).	% Coroutining
%:- use_module(library(clpq)).  % Constraints over rational numbers

validate_material(0).
validate_material(1).
validate_material(2).

validate_channel([0, Material]) :- validate_material(Material), !.
validate_channel([1, Material]) :- validate_material(Material), !.
validate_channel([2, Material]) :- validate_material(Material), !.

check_sequence_nocub(_, _, _, _, StartEdge, [], Buf, Buf, ActualEdge, [ActualEdge, _, _, _, _, _]) :-
    vvalidate_channel(StartEdge), !alidate_channel(ActualEdge), !.
check_sequence_nocub(_, _, _, _, StartEdge, [], Buf, Buf, ActualEdge, [_, ActualEdge, _, _, _, _]) :-
    validate_channel(StartEdge), !.
check_sequence_nocub(_, _, _, _, StartEdge, [], Buf, Buf, ActualEdge, [_, _, ActualEdge, _, _, _]) :-
    validate_channel(StartEdge), !.
check_sequence_nocub(_, _, _, _, StartEdge, [], Buf, Buf, ActualEdge, [_, _, _, ActualEdge, _, _]) :-
    validate_channel(StartEdge), !.
check_sequence_nocub(_, _, _, _, StartEdge, [], Buf, Buf, ActualEdge, [_, _, _, _, ActualEdge, _]) :-
    validate_channel(StartEdge), !.
check_sequence_nocub(_, _, _, _, StartEdge, [], Buf, Buf, ActualEdge, [_, _, _, _, _, ActualEdge]) :-
    validate_channel(StartEdge), !.

check_sequence(_, _, _, _, ActualEdge, [], Buf, Buf, ActualEdge, [ActualEdge, _, _, _, _, _]) :-
    validate_channel(ActualEdge), !.
check_sequence(_, _, _, _, ActualEdge, [], Buf, Buf, ActualEdge, [_, ActualEdge, _, _, _, _]) :-
    validate_channel(ActualEdge), !.
check_sequence(_, _, _, _, ActualEdge, [], Buf, Buf, ActualEdge, [_, _, ActualEdge, _, _, _]) :-
    validate_channel(ActualEdge), !.
check_sequence(_, _, _, _, ActualEdge, [], Buf, Buf, ActualEdge, [_, _, _, ActualEdge, _, _]) :-
    validate_channel(ActualEdge), !.
check_sequence(_, _, _, _, ActualEdge, [], Buf, Buf, ActualEdge, [_, _, _, _, ActualEdge, _]) :-
    validate_channel(ActualEdge), !.
check_sequence(_, _, _, _, ActualEdge, [], Buf, Buf, ActualEdge, [_, _, _, _, _, ActualEdge]) :-
    validate_channel(ActualEdge), !.

% edge 1 actual ---------------------------------------------------------------------------
check_sequence(N1, N2, N3, V, ActualEdge, [[CubN1, CubN2, CubN3, CubMaterial, CubCubs, [ActualEdge, Edge2, Edge3, Edge4, Edge5, Edge6]]| OtherCubs], Buf, Res, EndEdges, BoxEdges) :-
    validate_channel(ActualEdge),
    is_of_type(positive_integer, CubN1),
    is_of_type(positive_integer, CubN2),
    is_of_type(positive_integer, CubN3),
    N1 >= CubN1,
    N2 >= CubN2,
    N3 >= CubN3,
    V1 is V - CubN1 * CubN2 * CubN3,
    V1 >= 0,
    check_cub_correctness_find_min([CubN1, CubN2, CubN3, CubMaterial, CubCubs, [[], Edge2, Edge3, Edge4, Edge5, Edge6]], Buf, Res1, EndEdge, ActualEdge),
    min_list([Res1, Buf], Buf1),
    check_sequence(N1, N2, N3, V1, EndEdge, OtherCubs, Buf1, Res, EndEdges, BoxEdges), !.
% edge 2 actual -----------------------------------------------------------------------------------------------------------------
check_sequence(N1, N2, N3, V, ActualEdge, [[CubN1, CubN2, CubN3, CubMaterial, CubCubs, [Edge1, ActualEdge, Edge3, Edge4, Edge5, Edge6]]| OtherCubs], Buf, Res, EndEdges, BoxEdges) :-
    validate_channel(ActualEdge),
    is_of_type(positive_integer, CubN1),
    is_of_type(positive_integer, CubN2),
    is_of_type(positive_integer, CubN3),
    N1 >= CubN1,
    N2 >= CubN2,
    N3 >= CubN3,
    V1 is V - CubN1 * CubN2 * CubN3,
    V1 >= 0,
    check_cub_correctness_find_min([CubN1, CubN2, CubN3, CubMaterial, CubCubs, [Edge1, [], Edge3, Edge4, Edge5, Edge6]], Buf, Res1, EndEdge, ActualEdge),
    min_list([Res1, Buf], Buf1),
    check_sequence(N1, N2, N3, V1, EndEdge, OtherCubs, Buf1, Res, EndEdges, BoxEdges), !.
% edge 3 actual -----------------------------------------------------------------------------------------------------------------
check_sequence(N1, N2, N3, V, ActualEdge, [[CubN1, CubN2, CubN3, CubMaterial, CubCubs, [Edge1, Edge2, ActualEdge, Edge4, Edge5, Edge6]]| OtherCubs], Buf, Res, EndEdges, BoxEdges) :-
    validate_channel(ActualEdge),
    is_of_type(positive_integer, CubN1),
    is_of_type(positive_integer, CubN2),
    is_of_type(positive_integer, CubN3),
    N1 >= CubN1,
    N2 >= CubN2,
    N3 >= CubN3,
    V1 is V - CubN1 * CubN2 * CubN3,
    V1 >= 0,
    check_cub_correctness_find_min([CubN1, CubN2, CubN3, CubMaterial, CubCubs, [Edge1, Edge2, [], Edge4, Edge5, Edge6]], Buf, Res1, EndEdge, ActualEdge),
    min_list([Res1, Buf], Buf1),
    check_sequence(N1, N2, N3, V1, EndEdge, OtherCubs, Buf1, Res, EndEdges, BoxEdges), !.
% edge 5 actual -----------------------------------------------------------------------------------------------------------------
check_sequence(N1, N2, N3, V, ActualEdge, [[CubN1, CubN2, CubN3, CubMaterial, CubCubs, [Edge1, Edge2, Edge3, Edge4, ActualEdge, Edge6]]| OtherCubs], Buf, Res, EndEdges, BoxEdges) :-
    validate_channel(ActualEdge),
    is_of_type(positive_integer, CubN1),
    is_of_type(positive_integer, CubN2),
    is_of_type(positive_integer, CubN3),
    N1 >= CubN1,
    N2 >= CubN2,
    N3 >= CubN3,
    V1 is V - CubN1 * CubN2 * CubN3,
    V1 >= 0,
    check_cub_correctness_find_min([CubN1, CubN2, CubN3, CubMaterial, CubCubs, [Edge1, Edge2, Edge3, Edge4, [], Edge6]], Buf, Res1, EndEdge, ActualEdge),
    min_list([Res1, Buf], Buf1),
    check_sequence(N1, N2, N3, V1, EndEdge, OtherCubs, Buf1, Res, EndEdges, BoxEdges), !.
% edge 4 actual -----------------------------------------------------------------------------------------------------------------
check_sequence(N1, N2, N3, V, ActualEdge, [[CubN1, CubN2, CubN3, CubMaterial, CubCubs, [Edge1, Edge2, Edge3, ActualEdge, Edge5, Edge6]]| OtherCubs], Buf, Res, EndEdges, BoxEdges) :-
    validate_channel(ActualEdge),
    is_of_type(positive_integer, CubN1),
    is_of_type(positive_integer, CubN2),
    is_of_type(positive_integer, CubN3),
    N1 >= CubN1,
    N2 >= CubN2,
    N3 >= CubN3,
    V1 is V - CubN1 * CubN2 * CubN3,
    V1 >= 0,
    check_cub_correctness_find_min([CubN1, CubN2, CubN3, CubMaterial, CubCubs, [Edge1, Edge2, Edge3, [], Edge5, Edge6]], Buf, Res1, EndEdge, ActualEdge),
    min_list([Res1, Buf], Buf1),
    check_sequence(N1, N2, N3, V1, EndEdge, OtherCubs, Buf1, Res, EndEdges, BoxEdges), !.
% edge 6 actual -----------------------------------------------------------------------------------------------------------------
check_sequence(N1, N2, N3, V, ActualEdge, [[CubN1, CubN2, CubN3, CubMaterial, CubCubs, [Edge1, Edge2, Edge3, Edge4, Edge5, ActualEdge]]| OtherCubs], Buf, Res, EndEdges, BoxEdges) :-
    validate_channel(ActualEdge),
    is_of_type(positive_integer, CubN1),
    is_of_type(positive_integer, CubN2),
    is_of_type(positive_integer, CubN3),
    N1 >= CubN1,
    N2 >= CubN2,
    N3 >= CubN3,
    V1 is V - CubN1 * CubN2 * CubN3,
    V1 >= 0,
    check_cub_correctness_find_min([CubN1, CubN2, CubN3, CubMaterial, CubCubs, [Edge1, Edge2, Edge3, Edge4, Edge5, []]], Buf, Res1, EndEdge, ActualEdge),
    min_list([Res1, Buf], Buf1),
    check_sequence(N1, N2, N3, V1, EndEdge, OtherCubs, Buf1, Res, EndEdges, BoxEdges).

check_cub_correctness_find_min([N1, N2, N3, Material, [], Edges], Min, Res, EndEdge, StartEdge) :-
    is_of_type(positive_integer, Material),
    Min > Material,
    is_of_type(positive_integer, N1),
    is_of_type(positive_integer, N2),
    is_of_type(positive_integer, N3),
    V is N1 * N2 * N3,
    check_sequence_nocub(N1, N2, N3, V, StartEdge, [], Material, Res, EndEdge, Edges), !.
check_cub_correctness_find_min([N1, N2, N3, Material, [], Edges], Min, Res, EndEdge, StartEdge) :-
    is_of_type(positive_integer, N1),
    is_of_type(positive_integer, N2),
    is_of_type(positive_integer, N3),
    is_of_type(positive_integer, Material),
    V is N1 * N2 * N3,
    check_sequence_nocub(N1, N2, N3, V, StartEdge, [], Min, Res, EndEdge, Edges), !.
check_cub_correctness_find_min([N1, N2, N3, Material, Cubs, Edges], Min, Res, EndEdge, StartEdge) :-
    is_of_type(positive_integer, Material),
    Min > Material,
    is_of_type(positive_integer, N1),
    is_of_type(positive_integer, N2),
    is_of_type(positive_integer, N3),
    V is N1 * N2 * N3,
    check_sequence(N1, N2, N3, V, StartEdge, Cubs, Material, Res, EndEdge, Edges), !.
check_cub_correctness_find_min([N1, N2, N3, Material, Cubs, Edges], Min, Res, EndEdge, StartEdge) :-
    is_of_type(positive_integer, N1),
    is_of_type(positive_integer, N2),
    is_of_type(positive_integer, N3),
    is_of_type(positive_integer, Material),
    V is N1 * N2 * N3,
    check_sequence(N1, N2, N3, V, StartEdge, Cubs, Min, Res, EndEdge, Edges).

cub_fatigue([N1, N2, N3, Material, Cubs, [Edge1, Edge2, Edge3, Edge4, Edge5, Edge6]], Fatigue) :-
    check_cub_correctness_find_min([N1, N2, N3, Material, Cubs, [[], Edge2, Edge3, Edge4, Edge5, Edge6]], 10005000, Fatigue, _, Edge1), !.
cub_fatigue([N1, N2, N3, Material, Cubs, [Edge1, Edge2, Edge3, Edge4, Edge5, Edge6]], Fatigue) :-
    check_cub_correctness_find_min([N1, N2, N3, Material, Cubs, [Edge1, [], Edge3, Edge4, Edge5, Edge6]], 10005000, Fatigue, _, Edge2), !.
cub_fatigue([N1, N2, N3, Material, Cubs, [Edge1, Edge2, Edge3, Edge4, Edge5, Edge6]], Fatigue) :-
    check_cub_correctness_find_min([N1, N2, N3, Material, Cubs, [Edge1, Edge2, [], Edge4, Edge5, Edge6]], 10005000, Fatigue, _, Edge3), !.
cub_fatigue([N1, N2, N3, Material, Cubs, [Edge1, Edge2, Edge3, Edge4, Edge5, Edge6]], Fatigue) :-
    check_cub_correctness_find_min([N1, N2, N3, Material, Cubs, [Edge1, Edge2, Edge3, [], Edge5, Edge6]], 10005000, Fatigue, _, Edge4), !.
cub_fatigue([N1, N2, N3, Material, Cubs, [Edge1, Edge2, Edge3, Edge4, Edge5, Edge6]], Fatigue) :-
    check_cub_correctness_find_min([N1, N2, N3, Material, Cubs, [Edge1, Edge2, Edge3, Edge4, [], Edge6]], 10005000, Fatigue, _, Edge5), !.
cub_fatigue([N1, N2, N3, Material, Cubs, [Edge1, Edge2, Edge3, Edge4, Edge5, Edge6]], Fatigue) :-
    check_cub_correctness_find_min([N1, N2, N3, Material, Cubs, [Edge1, Edge2, Edge3, Edge4, Edge5, []]], 10005000, Fatigue, _, Edge6).

% Тест 1: 1 большой куб
% cub_fatigue([1, 2, 3, 5, [], [[], [1, 2], [1, 2] , [], [], []]], Fatigue)

% Тест 2: большой кубик и маленький кубик внутри
% cub_fatigue([1, 2, 3, 4, [[1, 1, 1, 2, [], [[1, 2], [0, 2], [], [], [], []]]], [[2, 1], [0, 2], [1, 2], [], [], []]], Fatigue).

% Тест 3: матрёшка из 5 кубиков
% cub_fatigue([1, 2, 3, 5, [[1, 1, 1, 4, [[1, 1, 1, 3, [[1, 1, 1, 2, [[1, 1, 1, 1, [], [[1, 2], [0, 2], [], [], [], []]]], [[1, 2], [0, 2], [], [], [], []]]], [[1, 2], [0, 2], [], [], [], []]]], [[1, 2], [0, 2], [], [], [], []]]], [[2, 1], [0, 2], [], [1, 2], [], []]], Fatigue)

% Тест 4: кубик внутри кубика больше по размеру, поместить нельзя
% cub_fatigue([1, 2, 3, 4, [[3, 2, 2, 2, [[1, 1, 1, 10, [], [[1, 2], [0, 2], [], [], [], []]]], [[1, 2], [0, 2], [], [], [], []]], [1, 1, 1, 1, [], [[1, 2], [0, 2], [], [], [], []]]], [[2, 1], [0, 2], [], [], [], [1, 2]]], Fatigue).

% Тест 5: внутри кубика 2 кубика и внутри одного из них кубик
% cub_fatigue([3, 3, 3, 4, [[3, 2, 2, 2, [[1, 1, 1, 10, [], [[1, 2], [0, 2], [], [], [], []]]], [[1, 2], [0, 2], [], [], [], []]], [1, 1, 1, 1, [], [[1, 2], [0, 2], [], [], [], []]]], [[2, 1], [1, 2], [], [], [1, 2], []]], Fatigue).

cub_fatigue_proc(Cub, Fatigue, true) :-
    cub_fatigue(Cub, Fatigue), !.
cub_fatigue_proc(Cub, Fatigue, false).


calc_data(Cub, OutputLabel) :-
    cub_fatigue_proc(Cub, Fatigue, ResExists),
    (   ResExists == true
    ->  send(OutputLabel, selection, Fatigue)
    ;   send(OutputLabel, selection, 'Error: No data or cub incorrect')
    ).

init_values([N1, N2, N3, Material, [], [IEdge1, IEdge2, IEdge3, IEdge4, IEdge5, IEdge6]], IN1, IN2, IN3, IMaterial, Edge1Has,  Edge1Material, Edge1Valve, Edge2Has, Edge2Material, Edge2Valve, Edge3Has, Edge3Material, Edge3Valve, Edge4Has, Edge4Material, Edge4Valve, Edge5Has, Edge5Material, Edge5Valve, Edge6Has, Edge6Material, Edge6Valve, true) :-
    atom_number(IN1, N1),
    atom_number(IN2, N2),
    atom_number(IN3, N3),
    is_of_type(positive_integer, N1),
    is_of_type(positive_integer, N2),
    is_of_type(positive_integer, N3),
    (
        IMaterial == 'Iron (fatigue 150h)' 
        -> Material is 150
        ; (IMaterial == 'Wood (fatigue 2h)' 
            -> Material is 2  
            ; Material is 1)
    ),
    (
        Edge1Has == 'Yes' 
        -> (Edge1Valve == 'type 1'
             ->  (Edge1Material == 'Optical Fiber'
                    -> IEdge1 = [0, 0]
                    ; (Edge1Material == 'Rubber' ->  IEdge1 = [0, 2] ; IEdge1 = [0, 1]) 
            )
             ; (Edge1Valve == 'type 2' 
                -> (Edge1Material == 'Optical Fiber'
                    -> IEdge1 = [1, 0]
                    ; (Edge1Material == 'Rubber' ->  IEdge1 = [1, 2] ; IEdge1 = [1, 1]) 
                    )
                ;
                    (Edge1Material == 'Optical Fiber'
                    ->  IEdge1 = [2, 0]
                    ; (Edge1Material == 'Rubber' ->  IEdge1 = [2, 2] ; IEdge1 = [2, 1]) 
                    )

                )
            ) 
        ; IEdge1 = []
    ),
    (
        Edge2Has == 'Yes' 
        -> (Edge2Valve == 'type 1'
            ->  (Edge2Material == 'Optical Fiber'
                -> IEdge2 = [0, 0]
                ; (Edge2Material == 'Rubber' ->  IEdge2 = [0, 2] ; IEdge2 = [0, 1]) 
        )
         ; (Edge2Valve == 'type 2' 
            -> (Edge2Material == 'Optical Fiber'
                ->  IEdge2 = [1, 0]
                ; (Edge2Material == 'Rubber' ->  IEdge2 = [1, 2] ; IEdge2 = [1, 1]) 
                )
            ;
                (Edge2Material == 'Optical Fiber'
                ->  IEdge2 = [2, 0]
                ; (Edge2Material == 'Rubber' ->  IEdge2 = [2, 2] ; IEdge2 = [2, 1]) 
                )

            )
        ) 
    ; IEdge2 = []
    ),
        (
        Edge3Has == 'Yes' 
        -> (Edge3Valve == 'type 1'
            ->  (Edge3Material == 'Optical Fiber'
                -> IEdge3 = [0, 0]
                ; (Edge3Material == 'Rubber' ->  IEdge3 = [0, 2] ; IEdge3 = [0, 1]) 
        )
         ; (Edge3Valve == 'type 2' 
            -> (Edge3Material == 'Optical Fiber'
                ->  IEdge3 = [1, 0]
                ; (Edge3Material == 'Rubber' ->  IEdge3 = [1, 2] ; IEdge3 = [1, 1]) 
                )
            ;
                (Edge3Material == 'Optical Fiber'
                ->  IEdge3 = [2, 0]
                ; (Edge3Material == 'Rubber' ->  IEdge3 = [2, 2] ; IEdge3 = [2, 1]) 
                )

            )
        ) 
    ; IEdge3 = []
    ),
     (
        Edge4Has == 'Yes' 
        -> (Edge4Valve == 'type 1'
            ->  (Edge4Material == 'Optical Fiber'
                -> IEdge4 = [0, 0]
                ; (Edge4Material == 'Rubber' ->  IEdge4 = [0, 2] ; IEdge4 = [0, 1]) 
        )
         ; (Edge4Valve == 'type 2' 
            -> (Edge4Material == 'Optical Fiber'
                ->  IEdge4 = [1, 0]
                ; (Edge4Material == 'Rubber' ->  IEdge4 = [1, 2] ; IEdge4 = [1, 1]) 
                )
            ;
                (Edge4Material == 'Optical Fiber'
                ->  IEdge4 = [2, 0]
                ; (Edge4Material == 'Rubber' ->  IEdge4 = [2, 2] ; IEdge4 = [2, 1]) 
                )

            )
        ) 
    ; IEdge4 = []
    ),
     (
        Edge5Has == 'Yes' 
        -> (Edge5Valve == 'type 1'
            ->  (Edge5Material == 'Optical Fiber'
                -> IEdge5 = [0, 0]
                ; (Edge5Material == 'Rubber' ->  IEdge5 = [0, 2] ; IEdge5 = [0, 1]) 
        )
         ; (Edge5Valve == 'type 2' 
            -> (Edge5Material == 'Optical Fiber'
                ->  IEdge5 = [1, 0]
                ; (Edge5Material == 'Rubber' ->  IEdge5 = [1, 2] ; IEdge5 = [1, 1]) 
                )
            ;
                (Edge5Material == 'Optical Fiber'
                ->  IEdge5 = [2, 0]
                ; (Edge5Material == 'Rubber' ->  IEdge5 = [2, 2] ; IEdge5 = [2, 1]) 
                )

            )
        ) 
    ; IEdge5 = []
    ),
     (
        Edge6Has == 'Yes' 
        -> (Edge6Valve == 'type 1'
            ->  (Edge6Material == 'Optical Fiber'
                -> IEdge6 = [0, 0]
                ; (Edge6Material == 'Rubber' ->  IEdge6 = [0, 2] ; IEdge6 = [0, 1]) 
        )
         ; (Edge6Valve == 'type 2' 
            -> (Edge6Material == 'Optical Fiber'
                ->  IEdge6 = [1, 0]
                ; (Edge6Material == 'Rubber' ->  IEdge6 = [1, 2] ; IEdge6 = [1, 1]) 
                )
            ;
                (Edge6Material == 'Optical Fiber'
                ->  IEdge6 = [2, 0]
                ; (Edge6Material == 'Rubber' ->  IEdge6 = [2, 2] ; IEdge6 = [2, 1]) 
                )
            )
        ) 
    ; IEdge6 = []
    ), !.

init_values([N1, N2, N3, Material, Cubs, [IEdge1, IEdge2, IEdge3, IEdge4, IEdge5, IEdge6]], IN1, IN2, IN3, IMaterial, Edge1Has,  Edge1Material, Edge1Valve, Edge2Has, Edge2Material, Edge2Valve, Edge3Has, Edge3Material, Edge3Valve, Edge4Has, Edge4Material, Edge4Valve, Edge5Has, Edge5Material, Edge5Valve, Edge6Has, Edge6Material, Edge6Valve, true) :-
    atom_number(IN1, N1),
    atom_number(IN2, N2),
    atom_number(IN3, N3),
    is_of_type(positive_integer, N1),
    is_of_type(positive_integer, N2),
    is_of_type(positive_integer, N3),
    (
        IMaterial == 'Iron (fatigue 150h)' 
        -> Material is 150
        ; (IMaterial == 'Wood (fatigue 2h)' 
            -> Material is 2  
            ; Material is 1)
    ),
    (
        Edge1Has == 'Yes' 
        -> (Edge1Valve == 'type 1'
             ->  (Edge1Material == 'Optical Fiber'
                    -> IEdge1 = [0, 0]
                    ; (Edge1Material == 'Rubber' ->  IEdge1 = [0, 2] ; IEdge1 = [0, 1]) 
            )
             ; (Edge1Valve == 'type 2' 
                -> (Edge1Material == 'Optical Fiber'
                    -> IEdge1 = [1, 0]
                    ; (Edge1Material == 'Rubber' ->  IEdge1 = [1, 2] ; IEdge1 = [1, 1]) 
                    )
                ;
                    (Edge1Material == 'Optical Fiber'
                    ->  IEdge1 = [2, 0]
                    ; (Edge1Material == 'Rubber' ->  IEdge1 = [2, 2] ; IEdge1 = [2, 1]) 
                    )

                )
            ) 
        ; IEdge1 = []
    ),
    (
        Edge2Has == 'Yes' 
        -> (Edge2Valve == 'type 1'
            ->  (Edge2Material == 'Optical Fiber'
                -> IEdge2 = [0, 0]
                ; (Edge2Material == 'Rubber' ->  IEdge2 = [0, 2] ; IEdge2 = [0, 1]) 
        )
         ; (Edge2Valve == 'type 2' 
            -> (Edge2Material == 'Optical Fiber'
                ->  IEdge2 = [1, 0]
                ; (Edge2Material == 'Rubber' ->  IEdge2 = [1, 2] ; IEdge2 = [1, 1]) 
                )
            ;
                (Edge2Material == 'Optical Fiber'
                ->  IEdge2 = [2, 0]
                ; (Edge2Material == 'Rubber' ->  IEdge2 = [2, 2] ; IEdge2 = [2, 1]) 
                )

            )
        ) 
    ; IEdge2 = []
    ),
        (
        Edge3Has == 'Yes' 
        -> (Edge3Valve == 'type 1'
            ->  (Edge3Material == 'Optical Fiber'
                -> IEdge3 = [0, 0]
                ; (Edge3Material == 'Rubber' ->  IEdge3 = [0, 2] ; IEdge3 = [0, 1]) 
        )
         ; (Edge3Valve == 'type 2' 
            -> (Edge3Material == 'Optical Fiber'
                ->  IEdge3 = [1, 0]
                ; (Edge3Material == 'Rubber' ->  IEdge3 = [1, 2] ; IEdge3 = [1, 1]) 
                )
            ;
                (Edge3Material == 'Optical Fiber'
                ->  IEdge3 = [2, 0]
                ; (Edge3Material == 'Rubber' ->  IEdge3 = [2, 2] ; IEdge3 = [2, 1]) 
                )

            )
        ) 
    ; IEdge3 = []
    ),
     (
        Edge4Has == 'Yes' 
        -> (Edge4Valve == 'type 1'
            ->  (Edge4Material == 'Optical Fiber'
                -> IEdge4 = [0, 0]
                ; (Edge4Material == 'Rubber' ->  IEdge4 = [0, 2] ; IEdge4 = [0, 1]) 
        )
         ; (Edge4Valve == 'type 2' 
            -> (Edge4Material == 'Optical Fiber'
                ->  IEdge4 = [1, 0]
                ; (Edge4Material == 'Rubber' ->  IEdge4 = [1, 2] ; IEdge4 = [1, 1]) 
                )
            ;
                (Edge4Material == 'Optical Fiber'
                ->  IEdge4 = [2, 0]
                ; (Edge4Material == 'Rubber' ->  IEdge4 = [2, 2] ; IEdge4 = [2, 1]) 
                )

            )
        ) 
    ; IEdge4 = []
    ),
     (
        Edge5Has == 'Yes' 
        -> (Edge5Valve == 'type 1'
            ->  (Edge5Material == 'Optical Fiber'
                -> IEdge5 = [0, 0]
                ; (Edge5Material == 'Rubber' ->  IEdge5 = [0, 2] ; IEdge5 = [0, 1]) 
        )
         ; (Edge5Valve == 'type 2' 
            -> (Edge5Material == 'Optical Fiber'
                ->  IEdge5 = [1, 0]
                ; (Edge5Material == 'Rubber' ->  IEdge5 = [1, 2] ; IEdge5 = [1, 1]) 
                )
            ;
                (Edge5Material == 'Optical Fiber'
                ->  IEdge5 = [2, 0]
                ; (Edge5Material == 'Rubber' ->  IEdge5 = [2, 2] ; IEdge5 = [2, 1]) 
                )

            )
        ) 
    ; IEdge5 = []
    ),
     (
        Edge6Has == 'Yes' 
        -> (Edge6Valve == 'type 1'
            ->  (Edge6Material == 'Optical Fiber'
                -> IEdge6 = [0, 0]
                ; (Edge6Material == 'Rubber' ->  IEdge6 = [0, 2] ; IEdge6 = [0, 1]) 
        )
         ; (Edge6Valve == 'type 2' 
            -> (Edge6Material == 'Optical Fiber'
                ->  IEdge6 = [1, 0]
                ; (Edge6Material == 'Rubber' ->  IEdge6 = [1, 2] ; IEdge6 = [1, 1]) 
                )
            ;
                (Edge6Material == 'Optical Fiber'
                ->  IEdge6 = [2, 0]
                ; (Edge6Material == 'Rubber' ->  IEdge6 = [2, 2] ; IEdge6 = [2, 1]) 
                )
            )
        ) 
    ; IEdge6 = []
    ), !.

init_values(_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, false).

check_values([N1, N2, N3, Material, Cubs, [IEdge1, IEdge2, IEdge3, IEdge4, IEdge5, IEdge6]], IN1, IN2, IN3, IMaterial, Edge1Has,  Edge1Material, Edge1Valve, Edge2Has, Edge2Material, Edge2Valve, Edge3Has, Edge3Material, Edge3Valve, Edge4Has, Edge4Material, Edge4Valve, Edge5Has, Edge5Material, Edge5Valve, Edge6Has, Edge6Material, Edge6Valve, Dialog, OutputLabel) :-
    init_values([N1, N2, N3, Material, Cubs, [IEdge1, IEdge2, IEdge3, IEdge4, IEdge5, IEdge6]], IN1, IN2, IN3, IMaterial, Edge1Has,  Edge1Material, Edge1Valve, Edge2Has, Edge2Material, Edge2Valve, Edge3Has, Edge3Material, Edge3Valve, Edge4Has, Edge4Material, Edge4Valve, Edge5Has, Edge5Material, Edge5Valve, Edge6Has, Edge6Material, Edge6Valve, Result),
    (   Result == true
    ->  send(Dialog, return, [N1, N2, N3, Material, Cubs, [IEdge1, IEdge2, IEdge3, IEdge4, IEdge5, IEdge6]])
    ;   send(OutputLabel, selection, 'Error: No data incorrect')
    ).

add_another_cube(Cubs, 0, Cubs) :- !.
add_another_cube(List, Count, Cubs) :- add_actual_cube(NewCub), NewCount is Count - 1, append(List, NewCub, Res), add_another_cube(Res, NewCount, Cubs), !.

add_cubs_1(Cubs, ICount) :-
    atom_number(ICount, Count),
    is_of_type(positive_integer, Count),
    add_actual_cube(NewCube),
    Count1 is Count - 1,
    add_another_cube([NewCube], Count1, Cubs), !.

add_actual_cube([N1, N2, N3, Material, Cubs, [IEdge1, IEdge2, IEdge3, IEdge4, IEdge5, IEdge6]]) :-
    new(Dialog, dialog('Add Cube')),
    send(Dialog, size, size(500, 850)),
    new(H1, dialog_group('Main cube date')),
    send(H1, size, size(480, 130)), 
    send(H1, append,  new(IN1, text_item(input_n1, ''))),
    send(H1, append, new(IN2, text_item(input_n2, ''))),
    send(H1, append, new(IN3, text_item(input_n3, ''))),
    send_list(H1, append, [new(Multiselect, menu("Material"))]),
    send_list(Multiselect, append, ['Iron (fatigue 150h)', 'Wood (fatigue 2h)', 'Glass (fatigue 1h)']),
    send(Dialog, append, H1),
    new(Edge1, dialog_group('Edge 1')),
    send_list(Edge1, append, [new(Edge1Multiselect0, menu("Has channel"))]),
    send_list(Edge1Multiselect0, append, ['Yes', 'No']),
    send_list(Edge1, append, [new(Edge1Multiselect1, menu("Material"))]),
    send_list(Edge1Multiselect1, append, ['Optical Fiber', 'Copper', 'Rubber']),
    send_list(Edge1, append, [new(Edge1Multiselect2, menu("Valve"))]),
    send_list(Edge1Multiselect2, append, ['type 1', 'type 2', 'type 3']),
    send(Dialog, append, Edge1),
    new(Edge2, dialog_group('Edge 2')),
    send_list(Edge2, append, [new(Edge2Multiselect0, menu("Has channel"))]),
    send_list(Edge2Multiselect0, append, ['Yes', 'No']),
    send_list(Edge2, append, [new(Edge2Multiselect1, menu("Material"))]),
    send_list(Edge2Multiselect1, append, ['Optical Fiber', 'Copper', 'Rubber']),
    send_list(Edge2, append, [new(Edge2Multiselect2, menu("Valve"))]),
    send_list(Edge2Multiselect2, append, ['type 1', 'type 2', 'type 3']),
    send(Dialog, append, Edge2),
    new(Edge3, dialog_group('Edge 3')),
    send_list(Edge3, append, [new(Edge3Multiselect0, menu("Has channel"))]),
    send_list(Edge3Multiselect0, append, ['Yes', 'No']),
    send_list(Edge3, append, [new(Edge3Multiselect1, menu("Material"))]),
    send_list(Edge3Multiselect1, append, ['Optical Fiber', 'Copper', 'Rubber']),
    send_list(Edge3, append, [new(Edge3Multiselect2, menu("Valve"))]),
    send_list(Edge3Multiselect2, append, ['type 1', 'type 2', 'type 3']),
    send(Dialog, append, Edge3),
    new(Edge4, dialog_group('Edge 4')),
    send_list(Edge4, append, [new(Edge4Multiselect0, menu("Has channel"))]),
    send_list(Edge4Multiselect0, append, ['Yes', 'No']),
    send_list(Edge4, append, [new(Edge4Multiselect1, menu("Material"))]),
    send_list(Edge4Multiselect1, append, ['Optical Fiber', 'Copper', 'Rubber']),
    send_list(Edge4, append, [new(Edge4Multiselect2, menu("Valve"))]),
    send_list(Edge4Multiselect2, append, ['type 1', 'type 2', 'type 3']),
    send(Dialog, append, Edge4),
    new(Edge5, dialog_group('Edge 5')),
    send_list(Edge5, append, [new(Edge5Multiselect0, menu("Has channel"))]),
    send_list(Edge5Multiselect0, append, ['Yes', 'No']),
    send_list(Edge5, append, [new(Edge5Multiselect1, menu("Material"))]),
    send_list(Edge5Multiselect1, append, ['Optical Fiber', 'Copper', 'Rubber']),
    send_list(Edge5, append, [new(Edge5Multiselect2, menu("Valve"))]),
    send_list(Edge5Multiselect2, append, ['type 1', 'type 2', 'type 3']),
    send(Dialog, append, Edge5),
    new(Edge6, dialog_group('Edge 6')),
    send_list(Edge6, append, [new(Edge6Multiselect0, menu("Has channel"))]),
    send_list(Edge6Multiselect0, append, ['Yes', 'No']),
    send_list(Edge6, append, [new(Edge6Multiselect1, menu("Material"))]),
    send_list(Edge6Multiselect1, append, ['Optical Fiber', 'Copper', 'Rubber']),
    send_list(Edge6, append, [new(Edge6Multiselect2, menu("Valve"))]),
    send_list(Edge6Multiselect2, append, ['type 1', 'type 2', 'type 3']),
    send(Dialog, append, Edge6),
    send(Dialog, append, new(OutputLabel1, label(output_text, ''))),
    send(Dialog, append,  new(Count, text_item(input_inside_blocks_count, ''))),
    send(Dialog, append, new(B2, button(add_cubes, message(@prolog, add_cubs_1,
                                                                        prolog(Cubs), Count?selection)))),
    send(Dialog, append, new(B1, button(save_data, message(@prolog, check_values,
                                                                        prolog([N1, N2, N3, Material, Cubs, [IEdge1, IEdge2, IEdge3, IEdge4, IEdge5, IEdge6]]),
                                                                        IN1?selection, 
                                                                        IN2?selection,
                                                                        IN3?selection,
                                                                        Multiselect?selection,
                                                                        Edge1Multiselect0?selection,
                                                                        Edge1Multiselect1?selection,
                                                                        Edge1Multiselect2?selection, 
                                                                        Edge2Multiselect0?selection,
                                                                        Edge2Multiselect1?selection,
                                                                        Edge2Multiselect2?selection, 
                                                                        Edge3Multiselect0?selection,
                                                                        Edge3Multiselect1?selection,
                                                                        Edge3Multiselect2?selection, 
                                                                        Edge4Multiselect0?selection,
                                                                        Edge4Multiselect1?selection,
                                                                        Edge4Multiselect2?selection, 
                                                                        Edge5Multiselect0?selection,
                                                                        Edge5M:wqultiselect1?selection,
                                                                        Edge5Multiselect2?selection, 
                                                                        Edge6Multiselect0?selection,
                                                                        Edge6Multiselect1?selection,
                                                                        Edge6Multiselect2?selection, 
                                                                        Dialog,
                                                                        OutputLabel1)))),
    get(Dialog, confirm, Answer), 
    send(Dialog, destroy),
    Answer \== @nil,
    write(Answer), nl,
    [N1, N2, N3, Material, Cubs, [IEdge1, IEdge2, IEdge3, IEdge4, IEdge5, IEdge6]] = Answer.


actual_cube(OutputLabel) :-
    add_actual_cube(Result),
    write(Result), nl,
    calc_data(Result, OutputLabel).

start_dialog(_Argv) :-
    new(Dialog, dialog('Main window')),
    send(Dialog, size, size(500, 500)),
    new(H1, dialog_group(' ')),
    send(H1, size, size(450, 450)), 
    send(Dialog, append, new(OutputLabel, label(output_text, ''))),
    send_list(H1, append, [
        new(B1, button(add_cube, message(@prolog, actual_cube, OutputLabel)))
    ]),

    send(Dialog, append, H1),
    send(Dialog, open).

main :-
   pce_main_loop(start_dialog).

:- initialization(main, main).
