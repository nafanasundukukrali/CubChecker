% Constraint Logic Programming
:- use_module(library(dif)).	% Sound inequality
:- use_module(library(clpfd)).	% Finite domain constraints
:- use_module(library(clpb)).	% Boolean constraints
:- use_module(library(chr)).	% Constraint Handling Rules
:- use_module(library(when)).	% Coroutining
%:- use_module(library(clpq)).  % Constraints over rational numbers

validate_material(0).
validate_material(1).
validate_material(2).

validate_channel([0, Material]) :- validate_material(Material), !.
validate_channel([1, Material]) :- validate_material(Material), !.
validate_channel([2, Material]) :- validate_material(Material), !.

check_sequence_1cub(_, _, _, _, _, [], Buf, Buf, ActualEdge, [ActualEdge, _, _, _, _, _]) :-
    validate_channel(ActualEdge), !.
check_sequence_1cub(_, _, _, _, _, [], Buf, Buf, ActualEdge, [_, ActualEdge, _, _, _, _]) :-
    validate_channel(ActualEdge), !.
check_sequence_1cub(_, _, _, _, _, [], Buf, Buf, ActualEdge, [_, _, ActualEdge, _, _, _]) :-
    validate_channel(ActualEdge), !.
check_sequence_1cub(_, _, _, _, _, [], Buf, Buf, ActualEdge, [_, _, _, ActualEdge, _, _]) :-
    validate_channel(ActualEdge), !.
check_sequence_1cub(_, _, _, _, _, [], Buf, Buf, ActualEdge, [_, _, _, _, ActualEdge, _]) :-
    validate_channel(ActualEdge), !.
check_sequence_1cub(_, _, _, _, _, [], Buf, Buf, ActualEdge, [_, _, _, _, _, ActualEdge]) :-
    validate_channel(ActualEdge), !.

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

% check_cub_correctness_find_min([_, _, _, Material, _, [[], [], [], [], [], []]], Min, Material, StartEdge, StartEdge) :-
%	Min > Material, !.
%check_cub_correctness_find_min([_, _, _, _, _, [[], [], [], [], [], []]], Min, Min, StartEdge, StartEdge) :- !.
check_cub_correctness_find_min([N1, N2, N3, Material, [], Edges], Min, Res, EndEdge, StartEdge) :-
    is_of_type(positive_integer, Material),
    Min > Material,
    is_of_type(positive_integer, N1),
    is_of_type(positive_integer, N2),
    is_of_type(positive_integer, N3),
    V is N1 * N2 * N3,
    check_sequence_1cub(N1, N2, N3, V, StartEdge, [], Material, Res, EndEdge, Edges), !.
check_cub_correctness_find_min([N1, N2, N3, Material, [], Edges], Min, Res, EndEdge, StartEdge) :-
    is_of_type(positive_integer, N1),
    is_of_type(positive_integer, N2),
    is_of_type(positive_integer, N3),
    is_of_type(positive_integer, Material),
    V is N1 * N2 * N3,
    check_sequence_1cub(N1, N2, N3, V, StartEdge, [], Min, Res, EndEdge, Edges), !.
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
