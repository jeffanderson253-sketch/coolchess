' ==========================================================================
'  COOL CHESS 1.3  -  a lean chess engine with a self-contained board UI
'  v1.3: mouse play, undo/redo, SAN/PGN/FEN, draw rules, stronger
'        evaluation/search, time controls, hints and a transposition table.
'  v1.2: full en passant support in move generation, search, make/unmake,
'        capture tracking and human move entry.
'  v1.1: pixel-art piece set (auto outline + drop shadow), UI polish,
'        opening eval terms and a tiny randomized 1-move opening book.
' ==========================================================================
'  Board: 64 ints, a1=0 ... h8=63.  Pieces: 1=P 2=N 3=B 4=R 5=Q 6=K.
'  Positive = White, negative = Black, 0 = empty.
'  Search:  negamax alpha-beta, quiescence, iterative deepening,
'           move ordering, PV, extensions and a Zobrist transposition table.
'  Eval:    material + compact positional terms (see Evaluate&).
' ==========================================================================
DefInt A-Z

Const VERSION$ = "1.3"
Const MAXPLY = 40 '  max search ply including quiescence
Const MAXMV = 220 '  max moves in one position
Const TTSIZE = 1048576
Const INF = 2000000
Const MATE = 1000000

Dim Shared B(63) '                board
Dim Shared Stm, CR, EpSq '        side to move (1/-1), castle rights bits (1=WK 2=WQ 4=BK 8=BQ), ep square (-1 = none)
Dim Shared WK, BK '               king squares
Dim Shared HumanSide, ViewSide, MaxDepth
Dim Shared LastFrom, LastTo, LastPromo, MoveCount, Thinking, SelectedSq
Dim Shared HalfClock, GameTop, RedoTop, ReplayingRedo, GameEnded, EnginePaused
Dim Shared EngineBadCount
Dim Shared MoveHistory$(512), SanHistory$(512), RedoMove$(512)
Dim Shared UiMessage$, UiAnalysis$, WhiteCaptures$, BlackCaptures$
Dim Shared GameResult$, GameReason$
Dim Shared InputLine$, InputActive
Dim Shared MF(MAXPLY, MAXMV), MT(MAXPLY, MAXMV), MP(MAXPLY, MAXMV) ' move lists per ply: from, to, promo piece
Dim Shared NM(MAXPLY), NC(MAXPLY) ' move count / noisy (capture+promo) count per ply; noisy moves sit at the front
Dim Shared UCap(MAXPLY), UCR(MAXPLY), UPc(MAXPLY), UEp(MAXPLY), UHalf(MAXPLY)
Dim Shared Nodes As Long
Dim Shared MatVal(6), Ctr(63)
Dim Shared KN(7, 1), KG(7, 1) '   knight offsets; king/slider dirs (0-3 straight, 4-7 diagonal)
Dim Shared SPR(6, 25, 21) '       22x26 piece sprites: 0 empty, 1 body, 2 inked detail
Dim Shared LegalMark(63), KillerMv(MAXPLY, 1) As Long
Dim Shared PVF(MAXPLY, MAXPLY), PVT(MAXPLY, MAXPLY), PVP(MAXPLY, MAXPLY), PVLen(MAXPLY)
Dim Shared SearchBestF, SearchBestT, SearchBestP, SearchDepthDone, StopSearch, StopMode
Dim Shared SearchScore As Long
Dim Shared SearchPV$, StopReason$
Dim Shared TimeBudget As Single, SearchStart As Single

' Game snapshots never share storage with the search undo arrays.
Dim Shared GB(512, 63), GS(512), GCR(512), GEp(512), GWK(512), GBK(512)
Dim Shared GLF(512), GLT(512), GLP(512), GMC(512), GHalf(512)
Dim Shared GWhite$(512), GBlack$(512)

' Zobrist keys and fixed-size transposition table.
Dim Shared ZPiece(12, 63) As _Unsigned _Integer64
Dim Shared ZCastle(15) As _Unsigned _Integer64
Dim Shared ZEp(7) As _Unsigned _Integer64
Dim Shared ZSide As _Unsigned _Integer64
Dim Shared PosHash As _Unsigned _Integer64
Dim Shared HashTemp As _Unsigned _Integer64
Dim Shared UHash(MAXPLY) As _Unsigned _Integer64
Dim Shared GHash(512) As _Unsigned _Integer64
Dim Shared HashLine(MAXPLY) As _Unsigned _Integer64
Dim Shared TTKey(TTSIZE - 1) As _Unsigned _Integer64
Dim Shared TTScore(TTSIZE - 1) As Long
Dim Shared TTMove(TTSIZE - 1) As Long
Dim Shared TTDepth(TTSIZE - 1), TTFlag(TTSIZE - 1)

' ----- one-time tables -----
Restore Offsets
For i = 0 To 7: Read KN(i, 0), KN(i, 1): Next
For i = 0 To 7: Read KG(i, 0), KG(i, 1): Next
MatVal(1) = 100: MatVal(2) = 300: MatVal(3) = 310
MatVal(4) = 500: MatVal(5) = 900: MatVal(6) = 0
For sq = 0 To 63 '                center table: 0 in the corners ... 6 in the middle
    Ctr(sq) = (14 - Abs(2 * (sq \ 8) - 7) - Abs(2 * (sq Mod 8) - 7)) \ 2
Next
Restore PieceArt '                load the 22x26 pixel-art piece sprites
For pc = 1 To 6
    For ry = 0 To 25
        Read art$
        For rx = 0 To 21
            ac$ = Mid$(art$, rx + 1, 1)
            If ac$ = "X" Then SPR(pc, ry, rx) = 1
            If ac$ = "o" Then SPR(pc, ry, rx) = 2
        Next
    Next
Next
Randomize Timer '                 for the little opening book and hash keys
InitHash

Screen _NewImage(1060, 660, 32)
_Title "Cool Chess " + VERSION$
_Font 16
_PrintMode _KeepBackground
MaxDepth = 5
HumanSide = 1
ViewSide = 1
TimeBudget = 0
InitGame
UiMessage$ = "New game. You are White. Enter a move such as e2e4."

' ----- main loop -----
Do
    UpdateGameState
    over = GameEnded

    If over = 0 And Stm <> HumanSide And EnginePaused = 0 Then
        DrawGameScreen
        EngineMove
    Else
        GetCommand c$, over
        c$ = LCase$(LTrim$(RTrim$(c$)))
        Select Case c$
            Case "quit", "q", "exit": End
            Case "help", "h"
                ShowHelp
                UiMessage$ = "Help closed. Enter a move or command."
            Case "new"
                InitGame
                HumanSide = 1
                ViewSide = 1
                UiMessage$ = "New game. You are White."
            Case "takeback", "back", "undo"
                TakeBack
            Case "redo"
                RedoMoves
            Case "pgn"
                ExportPGN
            Case "fen"
                UiMessage$ = "FEN: " + Fen$
            Case "d", "board"
                UiMessage$ = "Board refreshed."
            Case "flip"
                ViewSide = -ViewSide
                UiMessage$ = "Board flipped. " + SideName$(ViewSide) + " is now at the bottom."
            Case "eval"
                ev& = Evaluate&
                UiMessage$ = "Static evaluation: " + LTrim$(Str$(ev&)) + " cp (positive favors White)."
            Case "go"
                If over Then
                    UiMessage$ = "Game over - type 'new' to start again."
                ElseIf EnginePaused Then
                    EnginePaused = 0
                    UiMessage$ = "Engine search resumed."
                Else
                    HumanSide = -Stm
                    ViewSide = HumanSide
                    UiMessage$ = "The engine will play " + SideName$(Stm) + "; you are now " + SideName$(HumanSide) + "."
                End If
            Case "hint"
                If over Then
                    UiMessage$ = "Game over - no hint is available."
                Else
                    HintMove
                End If
            Case Else
                If over Then
                    UiMessage$ = "Game over - use pgn, fen, undo, new or quit."
                ElseIf Left$(c$, 6) = "depth " Then
                    n = Val(Mid$(c$, 7))
                    If n >= 1 And n <= 10 Then
                        MaxDepth = n
                        UiMessage$ = "Search depth set to " + LTrim$(Str$(n)) + "."
                    Else
                        UiMessage$ = "Depth must be from 1 through 10."
                    End If
                ElseIf Left$(c$, 5) = "time " Then
                    sec! = Val(Mid$(c$, 6))
                    If sec! >= 0 Then
                        TimeBudget = sec!
                        If TimeBudget = 0 Then
                            UiMessage$ = "Time control is off; depth controls the search."
                        Else
                            UiMessage$ = "Move time set to " + LTrim$(Str$(TimeBudget)) + " seconds."
                        End If
                    Else
                        UiMessage$ = "Time must be zero or a positive number of seconds."
                    End If
                ElseIf c$ <> "" Then
                    z = DoMove(c$) ' sets its own message when the move is bad
                End If
        End Select
    End If
Loop

End

Offsets:
Data 1,2,2,1,2,-1,1,-2,-1,-2,-2,-1,-2,1,-1,2
Data 1,0,-1,0,0,1,0,-1,1,1,1,-1,-1,1,-1,-1
BackRank:
Data 4,2,3,5,6,3,2,4
' ----- 22x26 pixel-art piece sprites ( . empty   X body   o inked detail )
PieceArt:
' pawn
Data "......................"
Data "......................"
Data "......................"
Data "......................"
Data "......................"
Data "......................"
Data "........XXXXXX........"
Data ".......XXXXXXXX......."
Data ".......XXXXXXXX......."
Data "........XXXXXX........"
Data "......XXXXXXXXXX......"
Data "........XXXXXX........"
Data "........XXXXXX........"
Data ".......XXXXXXXX......."
Data ".......XXXXXXXX......."
Data "......XXXXXXXXXX......"
Data "......XXXXXXXXXX......"
Data ".....XXXXXXXXXXXX....."
Data "....XXXXXXXXXXXXXX...."
Data "......................"
Data "....XXXXXXXXXXXXXX...."
Data "....XXXXXXXXXXXXXX...."
Data "....XXXXXXXXXXXXXX...."
Data "......................"
Data "......................"
Data "......................"
' knight
Data "......................"
Data "......XX..XX.........."
Data ".....XXXX.XXX........."
Data "....XXXXXXXXXX........"
Data "...XXXXXXXXXXXX......."
Data "...XXXXXXXXXXXXX......"
Data "..XXXXXXoXXXXXXXX....."
Data "..XXXXXXXXXXXXXXX....."
Data "..XXXXXXXXXXXXXXXX...."
Data ".XXXXXXXXXXXXXXXXX...."
Data ".XXXoXXXXXXXXXXXXX...."
Data ".XXXXX..XXXXXXXXXX...."
Data "..XXX...XXXXXXXXXX...."
Data "...X...XXXXXXXXXXX...."
Data "......XXXXXXXXXXXX...."
Data ".....XXXXXXXXXXXXX...."
Data ".....XXXXXXXXXXXXX...."
Data "....XXXXXXXXXXXXXX...."
Data "....XXXXXXXXXXXXXX...."
Data "...XXXXXXXXXXXXXXXX..."
Data "......................"
Data "...XXXXXXXXXXXXXXXX..."
Data "..XXXXXXXXXXXXXXXXXX.."
Data "..XXXXXXXXXXXXXXXXXX.."
Data "......................"
Data "......................"
' bishop
Data "..........XX.........."
Data ".........XXXX........."
Data "..........XX.........."
Data ".........XXXX........."
Data "........XXXXXX........"
Data ".......XXXXoXXX......."
Data ".......XXXoXXXX......."
Data "......XXXoXXXXXX......"
Data "......XXoXXXXXXX......"
Data "......XXXXXXXXXX......"
Data "......XXXXXXXXXX......"
Data ".......XXXXXXXX......."
Data "........XXXXXX........"
Data ".....XXXXXXXXXXXX....."
Data "........XXXXXX........"
Data "........XXXXXX........"
Data ".......XXXXXXXX......."
Data ".......XXXXXXXX......."
Data "......XXXXXXXXXX......"
Data ".....XXXXXXXXXXXX....."
Data "....XXXXXXXXXXXXXX...."
Data "...XXXXXXXXXXXXXXXX..."
Data "......................"
Data "..XXXXXXXXXXXXXXXXXX.."
Data "..XXXXXXXXXXXXXXXXXX.."
Data "......................"
' rook
Data "......................"
Data "......................"
Data "..XXX...XXXX...XXX...."
Data "..XXX...XXXX...XXX...."
Data "..XXXXXXXXXXXXXXXX...."
Data "..XXXXXXXXXXXXXXXX...."
Data "...XXXXXXXXXXXXXX....."
Data "....XXXXXXXXXXXX......"
Data "....XXXXXXXXXXXX......"
Data "....XXXXXXXXXXXX......"
Data "....XXXXXXXXXXXX......"
Data "....XXXXXXXXXXXX......"
Data "....XXXXXXXXXXXX......"
Data "....XXXXXXXXXXXX......"
Data "....XXXXXXXXXXXX......"
Data "....XXXXXXXXXXXX......"
Data "...XXXXXXXXXXXXXX....."
Data "..XXXXXXXXXXXXXXXX...."
Data "..XXXXXXXXXXXXXXXX...."
Data "......................"
Data ".XXXXXXXXXXXXXXXXXX..."
Data ".XXXXXXXXXXXXXXXXXX..."
Data "......................"
Data "......................"
Data "......................"
Data "......................"
' queen
Data "..XX......XX......XX.."
Data "..XX......XX......XX.."
Data "..XX..XX..XX..XX..XX.."
Data "..XX..XX..XX..XX..XX.."
Data "..XX..XX..XX..XX..XX.."
Data "..XXXXXXXXXXXXXXXXXX.."
Data "..XXXXXXXXXXXXXXXXXX.."
Data "...XXXXXXXXXXXXXXXX..."
Data "...XoXXXoXXXXoXXXoX..."
Data "....XXXXXXXXXXXXXX...."
Data ".....XXXXXXXXXXXX....."
Data "......XXXXXXXXXX......"
Data ".......XXXXXXXX......."
Data ".......XXXXXXXX......."
Data "......XXXXXXXXXX......"
Data "......XXXXXXXXXX......"
Data ".....XXXXXXXXXXXX....."
Data ".....XXXXXXXXXXXX....."
Data "....XXXXXXXXXXXXXX...."
Data "....XXXXXXXXXXXXXX...."
Data "...XXXXXXXXXXXXXXXX..."
Data "..XXXXXXXXXXXXXXXXXX.."
Data "......................"
Data "..XXXXXXXXXXXXXXXXXX.."
Data "..XXXXXXXXXXXXXXXXXX.."
Data "......................"
' king
Data "..........XX.........."
Data "..........XX.........."
Data "........XXXXXX........"
Data "..........XX.........."
Data "..........XX.........."
Data ".......XXXXXXXX......."
Data ".....XXXXXXXXXXXX....."
Data "....XXXXXXXXXXXXXX...."
Data "....XXXXXXXXXXXXXX...."
Data "....XoXXXoXXXXoXXX...."
Data "....XXXXXXXXXXXXXX...."
Data ".....XXXXXXXXXXXX....."
Data "......XXXXXXXXXX......"
Data ".......XXXXXXXX......."
Data ".......XXXXXXXX......."
Data "......XXXXXXXXXX......"
Data "......XXXXXXXXXX......"
Data ".....XXXXXXXXXXXX....."
Data ".....XXXXXXXXXXXX....."
Data "....XXXXXXXXXXXXXX...."
Data "...XXXXXXXXXXXXXXXX..."
Data "..XXXXXXXXXXXXXXXXXX.."
Data "......................"
Data "..XXXXXXXXXXXXXXXXXX.."
Data "..XXXXXXXXXXXXXXXXXX.."
Data "......................"

' ==========================================================================
Sub InitGame
    For i = 0 To 63: B(i) = 0: Next
    Restore BackRank
    For f = 0 To 7
        Read v
        B(f) = v: B(56 + f) = -v
        B(8 + f) = 1: B(48 + f) = -1
    Next
    Stm = 1: CR = 15: EpSq = -1
    WK = 4: BK = 60
    LastFrom = -1: LastTo = -1: LastPromo = 0
    MoveCount = 0: Thinking = 0: HalfClock = 0
    GameTop = 0: RedoTop = 0: ReplayingRedo = 0
    GameEnded = 0: GameResult$ = "*": GameReason$ = ""
    EnginePaused = 0: EngineBadCount = 0
    SelectedSq = -1
    For sq = 0 To 63: LegalMark(sq) = 0: Next
    For p = 0 To MAXPLY
        KillerMv(p, 0) = 0: KillerMv(p, 1) = 0
    Next
    ComputeHash
    UiAnalysis$ = "": WhiteCaptures$ = "": BlackCaptures$ = ""
End Sub

Sub ShowHelp
    _Display
    Cls , _RGB32(18, 21, 26)
    _PrintMode _KeepBackground
    Color _RGB32(236, 202, 116)
    _PrintString (42, 22), "COOL CHESS " + VERSION$ + " HELP"
    Color _RGB32(226, 229, 235)
    _PrintString (42, 52), "MOVE INPUT"
    _PrintString (62, 76), "Type e2e4, e2-e4 or o-o. Promotion: e7e8q (q/r/b/n)."
    _PrintString (62, 100), "Or click a piece and destination. Right-click or click it again to cancel."
    _PrintString (62, 124), "Mouse promotion defaults to queen; dots and rings mark legal destinations."
    Color _RGB32(236, 202, 116)
    _PrintString (42, 164), "GAME"
    Color _RGB32(226, 229, 235)
    _PrintString (62, 188), "new              New game as White"
    _PrintString (62, 212), "go               Engine plays the side to move"
    _PrintString (62, 236), "undo/back        Take back two plies (one if only one exists)"
    _PrintString (62, 260), "redo             Replay the plies from the last takeback"
    _PrintString (62, 284), "flip             Turn the board around"

    Color _RGB32(236, 202, 116)
    _PrintString (530, 164), "ENGINE"
    Color _RGB32(226, 229, 235)
    _PrintString (550, 188), "depth n          Search depth 1-10"
    _PrintString (550, 212), "time n           Seconds per move; 0 disables"
    _PrintString (550, 236), "hint             Recommend a move without playing"
    _PrintString (550, 260), "eval             Static White-view evaluation"
    _PrintString (550, 284), "SPACE / ESC      Move now / stop search"

    Color _RGB32(236, 202, 116)
    _PrintString (42, 326), "EXPORT AND DISPLAY"
    Color _RGB32(226, 229, 235)
    _PrintString (62, 350), "pgn              Write coolchess.pgn with SAN movetext"
    _PrintString (62, 374), "fen              Show the current FEN in the message panel"
    _PrintString (62, 398), "board / d        Refresh the board"
    _PrintString (62, 422), "help / h         This screen"
    _PrintString (62, 446), "quit / q         Exit"

    Color _RGB32(174, 181, 194)
    _PrintString (42, 510), "Ivory pieces are White; charcoal pieces are Black. Gold marks the latest move."
    _PrintString (42, 534), "Castling, en passant, promotion and draw rules are automatic."
    _PrintString (42, 558), "During engine search, SPACE uses the last completed depth; ESC leaves the position unchanged."
    Color _RGB32(236, 202, 116)
    _PrintString (42, 620), "Press any key to return to the game."
    _Display
    _AutoDisplay
    Do
        k$ = InKey$
    Loop While k$ <> ""
    Do
        k$ = InKey$
        _Limit 30
    Loop Until k$ <> ""
End Sub

Sub ShowBoard
    DrawGameScreen
End Sub

Sub NewRand64
    Dim x As _Unsigned _Integer64
    x = Int(Rnd * 65536)
    For i = 1 To 3
        x = x * 65536 + Int(Rnd * 65536)
    Next
    If x = 0 Then x = 1
    HashTemp = x
End Sub

Sub InitHash
    For p = 1 To 12
        For sq = 0 To 63
            NewRand64
            ZPiece(p, sq) = HashTemp
        Next
    Next
    For i = 0 To 15: NewRand64: ZCastle(i) = HashTemp: Next
    For i = 0 To 7: NewRand64: ZEp(i) = HashTemp: Next
    NewRand64: ZSide = HashTemp
End Sub

Function PieceIndex (p)
    If p > 0 Then PieceIndex = p Else PieceIndex = 6 + Abs(p)
End Function

Sub ComputeHash
    Dim h As _Unsigned _Integer64
    h = ZCastle(CR)
    If EpSq >= 0 Then h = h Xor ZEp(EpSq Mod 8)
    If Stm = -1 Then h = h Xor ZSide
    For sq = 0 To 63
        If B(sq) <> 0 Then h = h Xor ZPiece(PieceIndex(B(sq)), sq)
    Next
    PosHash = h
End Sub

Sub HashPiece (p, sq)
    If p <> 0 Then PosHash = PosHash Xor ZPiece(PieceIndex(p), sq)
End Sub

Sub PushGame
    If GameTop >= 512 Then Exit Sub
    GameTop = GameTop + 1
    For sq = 0 To 63: GB(GameTop, sq) = B(sq): Next
    GS(GameTop) = Stm: GCR(GameTop) = CR: GEp(GameTop) = EpSq
    GWK(GameTop) = WK: GBK(GameTop) = BK
    GLF(GameTop) = LastFrom: GLT(GameTop) = LastTo: GLP(GameTop) = LastPromo
    GMC(GameTop) = MoveCount: GHalf(GameTop) = HalfClock
    GWhite$(GameTop) = WhiteCaptures$: GBlack$(GameTop) = BlackCaptures$
    GHash(GameTop) = PosHash
End Sub

Sub RestoreGame (n)
    For sq = 0 To 63: B(sq) = GB(n, sq): Next
    Stm = GS(n): CR = GCR(n): EpSq = GEp(n)
    WK = GWK(n): BK = GBK(n)
    LastFrom = GLF(n): LastTo = GLT(n): LastPromo = GLP(n)
    MoveCount = GMC(n): HalfClock = GHalf(n)
    WhiteCaptures$ = GWhite$(n): BlackCaptures$ = GBlack$(n)
    PosHash = GHash(n)
    GameEnded = 0: GameResult$ = "*": GameReason$ = ""
    EnginePaused = 0
End Sub

Sub ClearRedo
    If ReplayingRedo Then Exit Sub
    RedoTop = 0
End Sub

Sub ClearSelection
    SelectedSq = -1
    For sq = 0 To 63: LegalMark(sq) = 0: Next
End Sub

Sub TakeBack
    If GameTop = 0 Then
        UiMessage$ = "Nothing to take back."
        Exit Sub
    End If
    n = 2
    If GameTop < n Then n = GameTop
    For k = 1 To n
        If RedoTop < 512 Then
            RedoTop = RedoTop + 1
            RedoMove$(RedoTop) = MoveHistory$(MoveCount)
        End If
        RestoreGame GameTop
        GameTop = GameTop - 1
    Next
    ClearSelection
    Thinking = 0
    EngineBadCount = 0
    If n = 1 Then
        UiMessage$ = "Took back one ply."
    Else
        UiMessage$ = "Took back two plies; it is " + SideName$(Stm) + " to move."
    End If
End Sub

Sub RedoMoves
    If RedoTop = 0 Then
        UiMessage$ = "Nothing to redo."
        Exit Sub
    End If
    n = 2
    If RedoTop < n Then n = RedoTop
    done = 0
    ReplayingRedo = -1
    For k = 1 To n
        raw$ = RedoMove$(RedoTop)
        RedoTop = RedoTop - 1
        If DoMove(raw$) Then
            done = done + 1
        Else
            Exit For
        End If
    Next
    ReplayingRedo = 0
    ClearSelection
    If GameEnded = 0 Then
        If done = 1 Then UiMessage$ = "Redid one ply."
        If done = 2 Then UiMessage$ = "Redid two plies."
    End If
End Sub

Function SameGamePosition (n)
    If GS(n) <> Stm Or GCR(n) <> CR Or GEp(n) <> EpSq Then Exit Function
    For sq = 0 To 63
        If GB(n, sq) <> B(sq) Then Exit Function
    Next
    SameGamePosition = -1
End Function

Function RepetitionCount
    n = 1 ' current position
    For i = 1 To GameTop
        If GHash(i) = PosHash Then
            If SameGamePosition(i) Then n = n + 1
        End If
    Next
    RepetitionCount = n
End Function

Function InsufficientMaterial
    minors = 0: bishops = 0: knights = 0
    wbSq = -1: bbSq = -1
    For sq = 0 To 63
        p = B(sq): a = Abs(p)
        If a = 1 Or a = 4 Or a = 5 Then Exit Function
        If a = 2 Then knights = knights + 1: minors = minors + 1
        If a = 3 Then
            bishops = bishops + 1: minors = minors + 1
            If p > 0 Then wbSq = sq Else bbSq = sq
        End If
    Next
    If minors = 0 Then InsufficientMaterial = -1: Exit Function
    If minors = 1 Then InsufficientMaterial = -1: Exit Function
    If minors = 2 And bishops = 2 And knights = 0 And wbSq >= 0 And bbSq >= 0 Then
        If ((wbSq \ 8) + (wbSq Mod 8)) Mod 2 = ((bbSq \ 8) + (bbSq Mod 8)) Mod 2 Then InsufficientMaterial = -1
    End If
End Function

Sub UpdateGameState
    If GameEnded Then Exit Sub
    If AnyLegal = 0 Then
        GameEnded = -1
        If InCheckNow Then
            If Stm = 1 Then
                GameResult$ = "0-1": UiMessage$ = "CHECKMATE - Black wins."
            Else
                GameResult$ = "1-0": UiMessage$ = "CHECKMATE - White wins."
            End If
            GameReason$ = "checkmate"
        Else
            GameResult$ = "1/2-1/2": GameReason$ = "stalemate"
            UiMessage$ = "STALEMATE - draw."
        End If
    ElseIf HalfClock >= 100 Then
        GameEnded = -1: GameResult$ = "1/2-1/2": GameReason$ = "fifty-move rule"
        UiMessage$ = "DRAW - fifty moves without a pawn move or capture."
    ElseIf RepetitionCount >= 3 Then
        GameEnded = -1: GameResult$ = "1/2-1/2": GameReason$ = "threefold repetition"
        UiMessage$ = "DRAW - threefold repetition."
    ElseIf InsufficientMaterial Then
        GameEnded = -1: GameResult$ = "1/2-1/2": GameReason$ = "insufficient material"
        UiMessage$ = "DRAW - insufficient mating material."
    End If
End Sub

Function SideName$ (s)
    If s = 1 Then SideName$ = "White" Else SideName$ = "Black"
End Function

Function CapturedBy$ (side)
    If side = 1 Then s$ = WhiteCaptures$ Else s$ = BlackCaptures$
    If s$ = "" Then s$ = "(none)"
    CapturedBy$ = s$
End Function

Sub RecordCapture (captured, movingSide)
    If captured = 0 Then Exit Sub
    ch$ = Mid$(" PNBRQK", Abs(captured) + 1, 1)
    If movingSide = 1 Then
        If WhiteCaptures$ <> "" Then WhiteCaptures$ = WhiteCaptures$ + " "
        WhiteCaptures$ = WhiteCaptures$ + ch$
    Else
        If BlackCaptures$ <> "" Then BlackCaptures$ = BlackCaptures$ + " "
        BlackCaptures$ = BlackCaptures$ + ch$
    End If
End Sub

Sub RecordMove (m$, san$)
    If MoveCount < 512 Then
        MoveCount = MoveCount + 1
        MoveHistory$(MoveCount) = m$
        SanHistory$(MoveCount) = san$
    End If
End Sub

Function MoveText$ (f0, t0, pr)
    m$ = Sq2$(f0) + Sq2$(t0)
    If pr Then m$ = m$ + Mid$(" pnbrq", pr + 1, 1)
    MoveText$ = m$
End Function

Function MakeSan$ (f0, t0, pr)
    p = B(f0): a = Abs(p)
    cap = (B(t0) <> 0)
    If a = 1 And t0 = EpSq And (f0 Mod 8) <> (t0 Mod 8) Then cap = -1
    If a = 6 And Abs(t0 - f0) = 2 Then
        If t0 > f0 Then san$ = "O-O" Else san$ = "O-O-O"
    ElseIf a = 1 Then
        san$ = ""
        If cap Then san$ = Chr$(97 + (f0 Mod 8)) + "x"
        san$ = san$ + Sq2$(t0)
        If pr Then san$ = san$ + "=" + Mid$(" PNBRQ", pr + 1, 1)
    Else
        san$ = Mid$(" PNBRQK", a + 1, 1)
        amb = 0: sameFile = 0: sameRank = 0
        Gen 1
        mi = 0
        For i = 1 To NM(1)
            If MF(1, i) = f0 And MT(1, i) = t0 And MP(1, i) = pr Then mi = i
            If MF(1, i) <> f0 And MT(1, i) = t0 Then
                If Abs(B(MF(1, i))) = a Then
                    MakeMove 1, i
                    bd = Bad
                    UnMake 1, i
                    If bd = 0 Then
                        amb = -1
                        If (MF(1, i) Mod 8) = (f0 Mod 8) Then sameFile = -1
                        If (MF(1, i) \ 8) = (f0 \ 8) Then sameRank = -1
                    End If
                End If
            End If
        Next
        If amb Then
            If sameFile = 0 Then
                san$ = san$ + Chr$(97 + (f0 Mod 8))
            ElseIf sameRank = 0 Then
                san$ = san$ + Chr$(49 + (f0 \ 8))
            Else
                san$ = san$ + Sq2$(f0)
            End If
        End If
        If cap Then san$ = san$ + "x"
        san$ = san$ + Sq2$(t0)
    End If

    ' The suffix needs the post-move position, but the base SAN above needed
    ' the untouched position for disambiguation.
    Gen 1
    mi = 0
    For i = 1 To NM(1)
        If MF(1, i) = f0 And MT(1, i) = t0 And MP(1, i) = pr Then mi = i: Exit For
    Next
    If mi > 0 Then
        MakeMove 1, mi
        If Bad = 0 Then
            If InCheckNow Then
                If AnyLegal = 0 Then san$ = san$ + "#" Else san$ = san$ + "+"
            End If
        End If
        UnMake 1, mi
    End If
    MakeSan$ = san$
End Function

Sub CommitMove (f0, t0, pr, movingSide, san$)
    Gen 0
    mi = 0
    For i = 1 To NM(0)
        If MF(0, i) = f0 And MT(0, i) = t0 And MP(0, i) = pr Then mi = i: Exit For
    Next
    If mi = 0 Then Exit Sub
    captured = B(t0)
    If Abs(B(f0)) = 1 And t0 = EpSq And captured = 0 Then captured = -movingSide
    If ReplayingRedo = 0 Then ClearRedo
    PushGame
    LastFrom = f0: LastTo = t0: LastPromo = pr
    MakeMove 0, mi
    RecordMove MoveText$(f0, t0, pr), san$
    RecordCapture captured, movingSide
    ClearSelection
    EnginePaused = 0
    UpdateGameState
End Sub

Function Fen$
    out$ = ""
    For r = 7 To 0 Step -1
        empty = 0
        For f = 0 To 7
            p = B(r * 8 + f)
            If p = 0 Then
                empty = empty + 1
            Else
                If empty Then out$ = out$ + LTrim$(Str$(empty)): empty = 0
                ch$ = Mid$("PNBRQK", Abs(p), 1)
                If p < 0 Then ch$ = LCase$(ch$)
                out$ = out$ + ch$
            End If
        Next
        If empty Then out$ = out$ + LTrim$(Str$(empty))
        If r > 0 Then out$ = out$ + "/"
    Next
    If Stm = 1 Then out$ = out$ + " w " Else out$ = out$ + " b "
    ca$ = ""
    If (CR And 1) Then ca$ = ca$ + "K"
    If (CR And 2) Then ca$ = ca$ + "Q"
    If (CR And 4) Then ca$ = ca$ + "k"
    If (CR And 8) Then ca$ = ca$ + "q"
    If ca$ = "" Then ca$ = "-"
    out$ = out$ + ca$ + " "
    If EpSq >= 0 Then out$ = out$ + Sq2$(EpSq) Else out$ = out$ + "-"
    out$ = out$ + " " + LTrim$(Str$(HalfClock))
    out$ = out$ + " " + LTrim$(Str$(MoveCount \ 2 + 1))
    Fen$ = out$
End Function

Sub ExportPGN
    d$ = Date$
    If Len(d$) = 10 Then
        pgnDate$ = Right$(d$, 4) + "." + Left$(d$, 2) + "." + Mid$(d$, 4, 2)
    Else
        pgnDate$ = "????.??.??"
    End If
    engine$ = "Cool Chess " + VERSION$
    If HumanSide = 1 Then
        white$ = "Human": black$ = engine$
    Else
        white$ = engine$: black$ = "Human"
    End If
    result$ = "*"
    If GameEnded Then result$ = GameResult$

    fn$ = "coolchess.pgn"
    qt$ = Chr$(34)
    Open fn$ For Output As #1
    Print #1, "[Event " + qt$ + "Cool Chess Game" + qt$ + "]"
    Print #1, "[Site " + qt$ + "Local" + qt$ + "]"
    Print #1, "[Date " + qt$ + pgnDate$ + qt$ + "]"
    Print #1, "[Round " + qt$ + "1" + qt$ + "]"
    Print #1, "[White " + qt$ + white$ + qt$ + "]"
    Print #1, "[Black " + qt$ + black$ + qt$ + "]"
    Print #1, "[Result " + qt$ + result$ + qt$ + "]"
    Print #1, ""
    pgnLine$ = ""
    For i = 1 To MoveCount
        If i Mod 2 = 1 Then
            tok$ = LTrim$(Str$((i + 1) \ 2)) + ". " + SanHistory$(i)
        Else
            tok$ = SanHistory$(i)
        End If
        If pgnLine$ = "" Then
            pgnLine$ = tok$
        ElseIf Len(pgnLine$) + Len(tok$) + 1 > 80 Then
            Print #1, pgnLine$
            pgnLine$ = tok$
        Else
            pgnLine$ = pgnLine$ + " " + tok$
        End If
    Next
    If pgnLine$ = "" Then
        pgnLine$ = result$
    ElseIf Len(pgnLine$) + Len(result$) + 1 > 80 Then
        Print #1, pgnLine$
        pgnLine$ = result$
    Else
        pgnLine$ = pgnLine$ + " " + result$
    End If
    Print #1, pgnLine$
    Close #1
    UiMessage$ = "PGN saved as " + fn$ + "."
End Sub

Sub DrawWrappedText (x, y, maxChars, t$, ink~&)
    rest$ = LTrim$(RTrim$(t$))
    yy = y
    Do While Len(rest$) > 0
        If Len(rest$) <= maxChars Then
            wrapLine$ = rest$
            rest$ = ""
        Else
            cut = maxChars
            Do While cut > 1 And Mid$(rest$, cut, 1) <> " "
                cut = cut - 1
            Loop
            If cut = 1 Then cut = maxChars
            wrapLine$ = RTrim$(Left$(rest$, cut))
            rest$ = LTrim$(Mid$(rest$, cut + 1))
        End If
        Color ink~&
        _PrintString (x, yy), wrapLine$
        yy = yy + 18
    Loop
End Sub

Function SprAt (a, ry, rx) ' sprite lookup with off-grid = empty (for outlining)
    If ry < 0 Or ry > 25 Or rx < 0 Or rx > 21 Then SprAt = 0 Else SprAt = SPR(a, ry, rx)
End Function

Sub DrawPieceSpr (cx, cy, p, sc, shadowed)
    ' Renders the 22x26 sprite for piece p centred on (cx, cy) at pixel scale
    ' sc.  Outlines are automatic: any body pixel touching empty space is
    ' drawn in the edge colour, so the silhouette always reads crisply.
    Dim face~&, edge~&, sh~&, c~&
    a = Abs(p)
    If p > 0 Then
        face~& = _RGB32(246, 241, 221)
        edge~& = _RGB32(42, 45, 51)
    Else
        face~& = _RGB32(39, 43, 50)
        edge~& = _RGB32(232, 227, 208)
    End If
    x0 = cx - 11 * sc: y0 = cy - 13 * sc
    If shadowed Then
        sh~& = _RGB32(10, 12, 15)
        For ry = 0 To 25
            For rx = 0 To 21
                If SPR(a, ry, rx) Then
                    Line (x0 + rx * sc + 2, y0 + ry * sc + 3)-(x0 + rx * sc + sc + 1, y0 + ry * sc + sc + 2), sh~&, BF
                End If
            Next
        Next
    End If
    For ry = 0 To 25
        For rx = 0 To 21
            v = SPR(a, ry, rx)
            If v Then
                If v = 2 Then
                    c~& = edge~& '                            inked detail (eye, slit, jewels)
                ElseIf SprAt(a, ry - 1, rx) = 0 Or SprAt(a, ry + 1, rx) = 0 Or SprAt(a, ry, rx - 1) = 0 Or SprAt(a, ry, rx + 1) = 0 Then
                    c~& = edge~& '                            automatic outline
                Else
                    c~& = face~&
                End If
                Line (x0 + rx * sc, y0 + ry * sc)-(x0 + rx * sc + sc - 1, y0 + ry * sc + sc - 1), c~&, BF
            End If
        Next
    Next
End Sub

Sub DrawPiece (cx, cy, p)
    DrawPieceSpr cx, cy, p, 2, 1
End Sub

Sub DrawCapturedRow (x, y, list$, side)
    ' Draw the captured pieces as miniature sprites instead of letters.
    ' side is the CAPTURING side, so its trophies are the other colour.
    n = 0
    For i = 1 To Len(list$)
        If Mid$(list$, i, 1) <> " " Then n = n + 1
    Next
    If n = 0 Then
        Color _RGB32(153, 161, 176)
        _PrintString (x, y + 2), "(none)"
        Exit Sub
    End If
    sp = 18
    If n > 1 And sp * n > 200 Then sp = 200 \ n '  overlap the tray when it fills up
    k = 0
    For i = 1 To Len(list$)
        ch$ = Mid$(list$, i, 1)
        idx = InStr("PNBRQK", ch$)
        If idx > 0 Then
            DrawPieceSpr x + 10 + k * sp, y + 13, -side * idx, 1, 0
            k = k + 1
        End If
    Next
End Sub

Sub DrawGameScreen
    Dim bg~&
    bx = 34: by = 56: ss = 56
    _Display
    Cls , _RGB32(18, 21, 26)
    _PrintMode _KeepBackground

    Color _RGB32(236, 202, 116)
    _PrintString (34, 20), "COOL CHESS " + VERSION$
    Color _RGB32(164, 172, 188)
    _PrintString (170, 20), "self-contained chess for QB64"

    checkSq = -1
    If InCheckNow Then
        If Stm = 1 Then checkSq = WK Else checkSq = BK
    End If

    Line (bx - 7, by - 7)-(bx + 8 * ss + 6, by + 8 * ss + 6), _RGB32(58, 49, 38), BF
    Line (bx - 7, by - 7)-(bx + 8 * ss + 6, by + 8 * ss + 6), _RGB32(126, 108, 80), B
    Line (bx - 5, by - 5)-(bx + 8 * ss + 4, by + 8 * ss + 4), _RGB32(24, 20, 16), B
    For dr = 0 To 7
        If ViewSide = 1 Then br = 7 - dr Else br = dr
        For dc = 0 To 7
            If ViewSide = 1 Then bf = dc Else bf = 7 - dc
            sq = br * 8 + bf
            If (br + bf) Mod 2 = 1 Then
                bg~& = _RGB32(207, 190, 153)
            Else
                bg~& = _RGB32(93, 116, 99)
            End If
            ring~& = 0
            If sq = LastFrom Then
                If (br + bf) Mod 2 = 1 Then bg~& = _RGB32(203, 181, 105) Else bg~& = _RGB32(139, 141, 74)
                ring~& = _RGB32(238, 201, 92)
            End If
            If sq = LastTo Then
                If (br + bf) Mod 2 = 1 Then bg~& = _RGB32(219, 192, 100) Else bg~& = _RGB32(158, 157, 76)
                ring~& = _RGB32(248, 213, 104)
            End If
            If sq = checkSq Then
                bg~& = _RGB32(184, 78, 72)
                ring~& = _RGB32(255, 128, 116)
            End If
            x = bx + dc * ss: y = by + dr * ss
            Line (x, y)-(x + ss - 1, y + ss - 1), bg~&, BF
            If sq = SelectedSq Then
                Line (x + 2, y + 2)-(x + ss - 3, y + ss - 3), _RGB32(104, 188, 255), B
                Line (x + 3, y + 3)-(x + ss - 4, y + ss - 4), _RGB32(104, 188, 255), B
            End If
            If ring~& <> 0 Then
                Line (x, y)-(x + ss - 1, y + ss - 1), ring~&, B
                Line (x + 1, y + 1)-(x + ss - 2, y + ss - 2), ring~&, B
            End If
            If LegalMark(sq) = 1 Then
                Circle (x + ss \ 2, y + ss \ 2), 5, _RGB32(60, 77, 82)
                Paint (x + ss \ 2, y + ss \ 2), _RGB32(60, 77, 82), _RGB32(60, 77, 82)
            ElseIf LegalMark(sq) = 2 Then
                Circle (x + ss \ 2, y + ss \ 2), 22, _RGB32(70, 151, 198)
                Circle (x + ss \ 2, y + ss \ 2), 21, _RGB32(70, 151, 198)
            End If
            If B(sq) <> 0 Then DrawPiece x + ss \ 2, y + ss \ 2, B(sq)
        Next
        Color _RGB32(206, 188, 140)
        _PrintString (bx - 22, by + dr * ss + 20), LTrim$(Str$(br + 1))
        _PrintString (bx + 8 * ss + 9, by + dr * ss + 20), LTrim$(Str$(br + 1))
    Next
    For dc = 0 To 7
        If ViewSide = 1 Then bf = dc Else bf = 7 - dc
        Color _RGB32(206, 188, 140)
        _PrintString (bx + dc * ss + 24, by - 23), Chr$(97 + bf)
        _PrintString (bx + dc * ss + 24, by + 8 * ss + 9), Chr$(97 + bf)
    Next
    Line (bx - 1, by - 1)-(bx + 8 * ss, by + 8 * ss), _RGB32(214, 206, 184), B

    px = 520: py = 56: pw = 510: ph = 470
    Line (px, py)-(px + pw, py + ph), _RGB32(27, 31, 38), BF
    Line (px, py)-(px + pw, py + ph), _RGB32(73, 80, 94), B

    Color _RGB32(236, 202, 116)
    _PrintString (px + 20, py + 14), "POSITION"
    Line (px + 20, py + 32)-(px + pw - 20, py + 32), _RGB32(62, 68, 80)
    Color _RGB32(226, 229, 235)
    _PrintString (px + 20, py + 40), "To move: " + SideName$(Stm)
    If Stm = 1 Then '            small swatch showing whose turn it is
        Line (px + 140, py + 42)-(px + 152, py + 54), _RGB32(246, 241, 221), BF
        Line (px + 140, py + 42)-(px + 152, py + 54), _RGB32(42, 45, 51), B
    Else
        Line (px + 140, py + 42)-(px + 152, py + 54), _RGB32(39, 43, 50), BF
        Line (px + 140, py + 42)-(px + 152, py + 54), _RGB32(232, 227, 208), B
    End If
    _PrintString (px + 20, py + 60), "You are:  " + SideName$(HumanSide)
    _PrintString (px + 20, py + 80), "View:     " + SideName$(ViewSide) + " at bottom"
    tc$ = "off"
    If TimeBudget > 0 Then tc$ = LTrim$(Str$(TimeBudget)) + "s"
    _PrintString (px + 260, py + 40), "Depth: " + LTrim$(Str$(MaxDepth)) + "  Time: " + tc$
    If MoveCount > 0 Then
        _PrintString (px + 260, py + 60), "Last: " + SanHistory$(MoveCount)
    Else
        _PrintString (px + 260, py + 60), "Last: (none)"
    End If
    If checkSq >= 0 Then
        Color _RGB32(255, 126, 116)
        _PrintString (px + 260, py + 80), "CHECK"
    ElseIf Thinking Then
        Color _RGB32(126, 203, 255)
        _PrintString (px + 260, py + 80), "ENGINE THINKING"
    End If

    Color _RGB32(236, 202, 116)
    _PrintString (px + 20, py + 108), "MESSAGE"
    Line (px + 20, py + 126)-(px + pw - 20, py + 126), _RGB32(62, 68, 80)
    DrawWrappedText px + 20, py + 132, 55, UiMessage$, _RGB32(226, 229, 235)

    Color _RGB32(236, 202, 116)
    _PrintString (px + 20, py + 192), "ENGINE ANALYSIS (WHITE VIEW)"
    Line (px + 20, py + 210)-(px + pw - 20, py + 210), _RGB32(62, 68, 80)
    If UiAnalysis$ = "" Then
        Color _RGB32(153, 161, 176)
        _PrintString (px + 20, py + 216), "No search completed yet."
    Else
        DrawWrappedText px + 20, py + 216, 55, UiAnalysis$, _RGB32(199, 214, 229)
    End If

    Color _RGB32(236, 202, 116)
    _PrintString (px + 20, py + 268), "MOVE HISTORY"
    Line (px + 20, py + 286)-(px + pw - 20, py + 286), _RGB32(62, 68, 80)
    If MoveCount = 0 Then
        Color _RGB32(153, 161, 176)
        _PrintString (px + 20, py + 294), "No moves yet."
    Else
        fullMoves = (MoveCount + 1) \ 2
        startMove = fullMoves - 7
        If startMove < 1 Then startMove = 1
        row = 0
        For mn = startMove To fullMoves
            histLine$ = Right$("   " + LTrim$(Str$(mn)), 3) + ".  "
            wi = 2 * mn - 1: bi = 2 * mn
            If wi <= MoveCount Then histLine$ = histLine$ + SanHistory$(wi)
            If bi <= MoveCount Then histLine$ = histLine$ + Space$(9 - Len(SanHistory$(wi))) + SanHistory$(bi)
            Color _RGB32(218, 222, 230)
            _PrintString (px + 20, py + 294 + row * 18), histLine$
            row = row + 1
        Next
    End If

    Color _RGB32(236, 202, 116)
    _PrintString (px + 220, py + 268), "CAPTURED"
    Color _RGB32(218, 222, 230)
    _PrintString (px + 220, py + 296), "White:"
    DrawCapturedRow px + 276, py + 290, WhiteCaptures$, 1
    Color _RGB32(218, 222, 230)
    _PrintString (px + 220, py + 328), "Black:"
    DrawCapturedRow px + 276, py + 322, BlackCaptures$, -1
    Color _RGB32(153, 161, 176)
    _PrintString (px + 220, py + 366), "Ivory pieces = White"
    _PrintString (px + 220, py + 388), "Charcoal pieces = Black"
    _PrintString (px + 220, py + 414), "Gold squares = last move"
    _PrintString (px + 220, py + 436), "Red square = king in check"

    Line (20, 538)-(1040, 582), _RGB32(27, 31, 38), BF
    Line (20, 538)-(1040, 582), _RGB32(73, 80, 94), B
    Color _RGB32(226, 229, 235)
    _PrintString (34, 547), "Move: type e2e4 or click squares     Promotion: e7e8q     Castling: o-o"
    Color _RGB32(164, 172, 188)
    _PrintString (34, 566), "Commands: help  undo  redo  hint  pgn  fen  go  depth 1-10  time n  quit"

    Line (20, 592)-(1040, 638), _RGB32(11, 14, 18), BF
    Line (20, 592)-(1040, 638), _RGB32(102, 113, 132), B
    If InputActive Then
        _PrintMode _FillBackground
        Color _RGB32(240, 243, 248), _RGB32(11, 14, 18)
        _PrintString (34, 607), InputLine$
        _PrintMode _KeepBackground
    End If
    _Display
    _AutoDisplay
End Sub

Sub SelectMouseSquare (sq)
    ClearSelection
    If sq < 0 Or sq > 63 Then Exit Sub
    If B(sq) = 0 Or Sgn(B(sq)) <> Stm Then Exit Sub
    SelectedSq = sq
    Gen 0
    For i = 1 To NM(0)
        If MF(0, i) = SelectedSq Then
            t0 = MT(0, i)
            cap = (B(t0) <> 0)
            If Abs(B(SelectedSq)) = 1 And t0 = EpSq And (SelectedSq Mod 8) <> (t0 Mod 8) Then cap = -1
            MakeMove 0, i
            bd = Bad
            UnMake 0, i
            If bd = 0 Then
                If cap Then LegalMark(t0) = 2 Else LegalMark(t0) = 1
            End If
        End If
    Next
End Sub

Function MouseBoardSquare (mx, my)
    bx = 34: by = 56: ss = 56
    MouseBoardSquare = -1
    If mx < bx Or mx >= bx + 8 * ss Or my < by Or my >= by + 8 * ss Then Exit Function
    dc = (mx - bx) \ ss: dr = (my - by) \ ss
    If ViewSide = 1 Then
        bf = dc: br = 7 - dr
    Else
        bf = 7 - dc: br = dr
    End If
    MouseBoardSquare = br * 8 + bf
End Function

Sub GetCommand (c$, over)
    c$ = ""
    lastL = 0: lastR = 0
    InputActive = -1
    Do
        If over Then
            prompt$ = "Game over > "
        ElseIf Stm = 1 Then
            prompt$ = "White move > "
        Else
            prompt$ = "Black move > "
        End If
        InputLine$ = prompt$ + c$ + "_"
        DrawGameScreen

        k$ = InKey$
        If k$ <> "" Then
            If k$ = Chr$(13) Then
                ClearSelection
                InputActive = 0
                Exit Sub
            ElseIf k$ = Chr$(8) Then
                If Len(c$) > 0 Then c$ = Left$(c$, Len(c$) - 1)
            ElseIf Len(k$) = 1 Then
                If Asc(k$) >= 32 And Asc(k$) <= 126 And Len(c$) < 100 Then c$ = c$ + k$
            End If
        End If

        lb = 0: rb = 0
        Do While _MouseInput
            mx = _MouseX: my = _MouseY
            lb = _MouseButton(1): rb = _MouseButton(2)
            If rb And lastR = 0 Then ClearSelection
            If over = 0 And lb And lastL = 0 Then
                sq = MouseBoardSquare(mx, my)
                If sq >= 0 Then
                    If SelectedSq < 0 Then
                        SelectMouseSquare sq
                    ElseIf sq = SelectedSq Then
                        ClearSelection
                    ElseIf LegalMark(sq) > 0 Then
                        c$ = Sq2$(SelectedSq) + Sq2$(sq)
                        If Abs(B(SelectedSq)) = 1 Then
                            If sq \ 8 = 0 Or sq \ 8 = 7 Then c$ = c$ + "q"
                        End If
                        ClearSelection
                        InputActive = 0
                        Exit Sub
                    ElseIf B(sq) <> 0 And Sgn(B(sq)) = Stm Then
                        SelectMouseSquare sq
                    Else
                        ClearSelection
                    End If
                End If
            End If
            lastL = lb: lastR = rb
        Loop
        lastL = _MouseButton(1)
        lastR = _MouseButton(2)
        _Limit 60
    Loop
End Sub

Function Sq2$ (sq)
    Sq2$ = Chr$(97 + (sq Mod 8)) + Chr$(49 + (sq \ 8))
End Function

Function MvStr$ (ply, i)
    MvStr$ = MoveText$(MF(ply, i), MT(ply, i), MP(ply, i))
End Function

' ----- move list building ------------------------------------------------
Sub AddMv (ply, f0, t0, pr)
    n = NM(ply) + 1
    If n > MAXMV Then Exit Sub
    NM(ply) = n
    MF(ply, n) = f0: MT(ply, n) = t0: MP(ply, n) = pr
    isEp = 0
    If Abs(B(f0)) = 1 And t0 = EpSq Then
        If (f0 Mod 8) <> (t0 Mod 8) Then isEp = 1
    End If
    If B(t0) <> 0 Or pr <> 0 Or isEp Then ' captures/promotions first = free move ordering
        NC(ply) = NC(ply) + 1
        k = NC(ply)
        If k <> n Then
            Swap MF(ply, n), MF(ply, k)
            Swap MT(ply, n), MT(ply, k)
            Swap MP(ply, n), MP(ply, k)
        End If
    End If
End Sub

Sub AddProms (ply, f0, t0)
    AddMv ply, f0, t0, 5
    AddMv ply, f0, t0, 2
    AddMv ply, f0, t0, 4
    AddMv ply, f0, t0, 3
End Sub

Function MoveCode& (f0, t0, pr)
    MoveCode& = CLng(f0) * 4096 + CLng(t0) * 64 + pr
End Function

Sub DecodeMove (code&, f0, t0, pr)
    f0 = code& \ 4096
    restCode& = code& Mod 4096
    t0 = restCode& \ 64
    pr = restCode& Mod 64
End Sub

Function MoveOrderScore& (ply, i)
    attacker = Abs(B(MF(ply, i)))
    victim = Abs(B(MT(ply, i)))
    If victim = 0 And attacker = 1 And MT(ply, i) = EpSq Then victim = 1
    score& = CLng(MatVal(victim)) * 8 - MatVal(attacker)
    promo = MP(ply, i)
    If promo <> 0 Then score& = score& + MatVal(promo) * 8
    MoveOrderScore& = score&
End Function

Sub SwapMove (ply, a, b)
    If a = b Then Exit Sub
    Swap MF(ply, a), MF(ply, b)
    Swap MT(ply, a), MT(ply, b)
    Swap MP(ply, a), MP(ply, b)
End Sub

Sub BringMove (ply, f0, t0, pr, target)
    If target < 1 Or target > NM(ply) Then Exit Sub
    For i = target To NM(ply)
        If MF(ply, i) = f0 And MT(ply, i) = t0 And MP(ply, i) = pr Then
            SwapMove ply, i, target
            Exit Sub
        End If
    Next
End Sub

Sub OrderMoves (ply)
    ' MVV-LVA inside the noisy block; killer quiets follow it.
    For i = 1 To NC(ply) - 1
        best = i: bs& = MoveOrderScore&(ply, i)
        For j = i + 1 To NC(ply)
            sc& = MoveOrderScore&(ply, j)
            If sc& > bs& Then best = j: bs& = sc&
        Next
        SwapMove ply, i, best
    Next
    slot = NC(ply) + 1
    For k = 0 To 1
        If KillerMv(ply, k) <> 0 And slot <= NM(ply) Then
            DecodeMove KillerMv(ply, k), f0, t0, pr
            For i = slot To NM(ply)
                If MF(ply, i) = f0 And MT(ply, i) = t0 And MP(ply, i) = pr Then
                    SwapMove ply, i, slot
                    slot = slot + 1
                    Exit For
                End If
            Next
        End If
    Next
End Sub

' Generate pseudo-legal moves for the side to move (legality = king safety
' is tested after MakeMove via Bad).  Castling is fully verified here.
Sub Gen (ply)
    NM(ply) = 0: NC(ply) = 0
    For sq = 0 To 63
        p = B(sq)
        If p <> 0 And Sgn(p) = Stm Then
            a = Abs(p): r = sq \ 8: f = sq Mod 8
            Select Case a
                Case 1 ' ---- pawn ----
                    nr = r + Stm
                    t = nr * 8 + f
                    If B(t) = 0 Then
                        If nr = 0 Or nr = 7 Then
                            AddProms ply, sq, t
                        Else
                            AddMv ply, sq, t, 0
                            If (Stm = 1 And r = 1) Or (Stm = -1 And r = 6) Then
                                If B((r + 2 * Stm) * 8 + f) = 0 Then AddMv ply, sq, (r + 2 * Stm) * 8 + f, 0
                            End If
                        End If
                    End If
                    For df = -1 To 1 Step 2
                        nf = f + df
                        If nf >= 0 And nf <= 7 Then
                            t = nr * 8 + nf
                            If B(t) <> 0 And Sgn(B(t)) = -Stm Then
                                If nr = 0 Or nr = 7 Then AddProms ply, sq, t Else AddMv ply, sq, t, 0
                            ElseIf t = EpSq Then
                                ' The pawn being captured is beside us, not on the destination square.
                                capSq = t - 8 * Stm
                                If B(capSq) = -Stm Then AddMv ply, sq, t, 0
                            End If
                        End If
                    Next
                Case 2 ' ---- knight ----
                    For i = 0 To 7
                        nr = r + KN(i, 0): nf = f + KN(i, 1)
                        If nr >= 0 And nr <= 7 And nf >= 0 And nf <= 7 Then
                            t = nr * 8 + nf
                            If Sgn(B(t)) <> Stm Then AddMv ply, sq, t, 0
                        End If
                    Next
                Case 3, 4, 5 ' ---- bishop / rook / queen ----
                    i1 = 0: i2 = 7
                    If a = 4 Then i2 = 3 '  rook: straight dirs only
                    If a = 3 Then i1 = 4 '  bishop: diagonals only
                    For i = i1 To i2
                        nr = r: nf = f
                        Do
                            nr = nr + KG(i, 0): nf = nf + KG(i, 1)
                            If nr < 0 Or nr > 7 Or nf < 0 Or nf > 7 Then Exit Do
                            t = nr * 8 + nf
                            If B(t) = 0 Then
                                AddMv ply, sq, t, 0
                            Else
                                If Sgn(B(t)) = -Stm Then AddMv ply, sq, t, 0
                                Exit Do
                            End If
                        Loop
                    Next
                Case 6 ' ---- king ----
                    For i = 0 To 7
                        nr = r + KG(i, 0): nf = f + KG(i, 1)
                        If nr >= 0 And nr <= 7 And nf >= 0 And nf <= 7 Then
                            t = nr * 8 + nf
                            If Sgn(B(t)) <> Stm Then AddMv ply, sq, t, 0
                        End If
                    Next
                    ' castling: rights + empty path + king may not pass through check
                    If Stm = 1 And sq = 4 Then
                        If (CR And 1) Then
                            If B(5) = 0 And B(6) = 0 Then
                                If Atk(4, -1) = 0 And Atk(5, -1) = 0 And Atk(6, -1) = 0 Then AddMv ply, 4, 6, 0
                            End If
                        End If
                        If (CR And 2) Then
                            If B(3) = 0 And B(2) = 0 And B(1) = 0 Then
                                If Atk(4, -1) = 0 And Atk(3, -1) = 0 And Atk(2, -1) = 0 Then AddMv ply, 4, 2, 0
                            End If
                        End If
                    ElseIf Stm = -1 And sq = 60 Then
                        If (CR And 4) Then
                            If B(61) = 0 And B(62) = 0 Then
                                If Atk(60, 1) = 0 And Atk(61, 1) = 0 And Atk(62, 1) = 0 Then AddMv ply, 60, 62, 0
                            End If
                        End If
                        If (CR And 8) Then
                            If B(59) = 0 And B(58) = 0 And B(57) = 0 Then
                                If Atk(60, 1) = 0 And Atk(59, 1) = 0 And Atk(58, 1) = 0 Then AddMv ply, 60, 58, 0
                            End If
                        End If
                    End If
            End Select
        End If
    Next
    OrderMoves ply
End Sub

' Is square sq attacked by side s? En passant needs no special case here:
' pawns still attack their normal diagonal squares.
Function Atk (sq, s)
    r = sq \ 8: f = sq Mod 8
    pr = r - s ' rank an attacking pawn would sit on
    If pr >= 0 And pr <= 7 Then
        If f > 0 Then If B(pr * 8 + f - 1) = s Then Atk = 1: Exit Function
        If f < 7 Then If B(pr * 8 + f + 1) = s Then Atk = 1: Exit Function
    End If
    For i = 0 To 7 ' knights
        nr = r + KN(i, 0): nf = f + KN(i, 1)
        If nr >= 0 And nr <= 7 And nf >= 0 And nf <= 7 Then
            If B(nr * 8 + nf) = 2 * s Then Atk = 1: Exit Function
        End If
    Next
    For i = 0 To 7 ' sliders, plus adjacent enemy king on the first step
        nr = r: nf = f: st = 0
        Do
            nr = nr + KG(i, 0): nf = nf + KG(i, 1): st = st + 1
            If nr < 0 Or nr > 7 Or nf < 0 Or nf > 7 Then Exit Do
            q = B(nr * 8 + nf)
            If q <> 0 Then
                If Sgn(q) = s Then
                    aq = Abs(q)
                    If aq = 5 Then Atk = 1: Exit Function
                    If st = 1 And aq = 6 Then Atk = 1: Exit Function
                    If i < 4 And aq = 4 Then Atk = 1: Exit Function
                    If i > 3 And aq = 3 Then Atk = 1: Exit Function
                End If
                Exit Do
            End If
        Loop
    Next
    Atk = 0
End Function

' ----- make / unmake ------------------------------------------------------
Sub MakeMove (ply, i)
    f0 = MF(ply, i): t0 = MT(ply, i): pr = MP(ply, i)
    p = B(f0)
    UPc(ply) = p: UCap(ply) = B(t0): UCR(ply) = CR: UEp(ply) = EpSq
    UHalf(ply) = HalfClock: UHash(ply) = PosHash
    captured = B(t0): isEp = 0
    If Abs(p) = 1 And t0 = EpSq And B(t0) = 0 Then
        If (f0 Mod 8) <> (t0 Mod 8) Then isEp = -1
    End If

    PosHash = PosHash Xor ZCastle(CR)
    If EpSq >= 0 Then PosHash = PosHash Xor ZEp(EpSq Mod 8)
    HashPiece p, f0
    If captured <> 0 Then HashPiece captured, t0
    ' En passant: a pawn moves diagonally to the empty EpSq and removes
    ' the enemy pawn from the square it just passed to.
    If isEp Then
        capSq = t0 - 8 * Stm
        HashPiece B(capSq), capSq
        B(capSq) = 0
    End If
    B(t0) = p: B(f0) = 0
    If pr Then B(t0) = pr * Stm
    HashPiece B(t0), t0
    If p = 6 Then WK = t0
    If p = -6 Then BK = t0
    If Abs(p) = 6 Then ' castling: move the rook too
        If t0 - f0 = 2 Then
            HashPiece B(t0 + 1), t0 + 1
            B(t0 - 1) = B(t0 + 1): B(t0 + 1) = 0
            HashPiece B(t0 - 1), t0 - 1
        End If
        If f0 - t0 = 2 Then
            HashPiece B(t0 - 2), t0 - 2
            B(t0 + 1) = B(t0 - 2): B(t0 - 2) = 0
            HashPiece B(t0 + 1), t0 + 1
        End If
    End If
    ' castle rights die when king/rook moves or a rook is captured
    If f0 = 4 Then CR = CR And 12
    If f0 = 60 Then CR = CR And 3
    If f0 = 7 Or t0 = 7 Then CR = CR And 14
    If f0 = 0 Or t0 = 0 Then CR = CR And 13
    If f0 = 63 Or t0 = 63 Then CR = CR And 11
    If f0 = 56 Or t0 = 56 Then CR = CR And 7
    EpSq = -1
    If Abs(p) = 1 And Abs(t0 - f0) = 16 Then EpSq = (f0 + t0) \ 2
    If Abs(p) = 1 Or captured <> 0 Or isEp Then HalfClock = 0 Else HalfClock = HalfClock + 1
    Stm = -Stm
    PosHash = PosHash Xor ZCastle(CR)
    If EpSq >= 0 Then PosHash = PosHash Xor ZEp(EpSq Mod 8)
    PosHash = PosHash Xor ZSide
End Sub

Sub UnMake (ply, i)
    Stm = -Stm
    f0 = MF(ply, i): t0 = MT(ply, i)
    p = UPc(ply)
    B(f0) = p: B(t0) = UCap(ply)
    ' Restore the pawn removed by an en passant capture.
    If Abs(p) = 1 And t0 = UEp(ply) And UCap(ply) = 0 Then
        If (f0 Mod 8) <> (t0 Mod 8) Then B(t0 - 8 * Stm) = -Stm
    End If
    CR = UCR(ply): EpSq = UEp(ply)
    If p = 6 Then WK = f0
    If p = -6 Then BK = f0
    If Abs(p) = 6 Then
        If t0 - f0 = 2 Then B(t0 + 1) = B(t0 - 1): B(t0 - 1) = 0
        If f0 - t0 = 2 Then B(t0 - 2) = B(t0 + 1): B(t0 + 1) = 0
    End If
    HalfClock = UHalf(ply)
    PosHash = UHash(ply)
End Sub

' After MakeMove: did the side that just moved leave its king in check?
Function Bad
    If Stm = 1 Then ks = BK Else ks = WK
    Bad = Atk(ks, Stm)
End Function

Function InCheckNow ' is the side to move in check right now?
    If Stm = 1 Then InCheckNow = Atk(WK, -1) Else InCheckNow = Atk(BK, 1)
End Function

Function AnyLegal ' does the side to move have any legal move?
    Gen 0
    For i = 1 To NM(0)
        MakeMove 0, i
        bd = Bad
        UnMake 0, i
        If bd = 0 Then AnyLegal = 1: Exit Function
    Next
    AnyLegal = 0
End Function

' ----- evaluation (White-positive centipawns) -----------------------------
' Keep everything here.  Add terms freely; the search never needs changing.
Function Evaluate&
    Dim s As Long
    Dim WPF(7), BPF(7), WMost(7), BMost(7), WLow(7), BHigh(7)
    Dim PassBonus(7)
    s = 0
    For f = 0 To 7
        WMost(f) = -1: BMost(f) = 8
        WLow(f) = 8: BHigh(f) = -1
    Next
    phase = 0
    For sq = 0 To 63
        p = B(sq): r = sq \ 8: f = sq Mod 8
        If p = 1 Then
            WPF(f) = WPF(f) + 1
            If r > WMost(f) Then WMost(f) = r
            If r < WLow(f) Then WLow(f) = r
        ElseIf p = -1 Then
            BPF(f) = BPF(f) + 1
            If r < BMost(f) Then BMost(f) = r
            If r > BHigh(f) Then BHigh(f) = r
        ElseIf p <> 0 And Abs(p) <> 6 Then
            phase = phase + MatVal(Abs(p))
        End If
    Next
    PassBonus(1) = 10: PassBonus(2) = 15: PassBonus(3) = 25
    PassBonus(4) = 40: PassBonus(5) = 65: PassBonus(6) = 100
    endgame = (phase < 1400)
    wLight = 0: wDark = 0: bLight = 0: bDark = 0

    For sq = 0 To 63
        p = B(sq)
        If p <> 0 Then
            a = Abs(p)
            v = MatVal(a)
            r = sq \ 8: f = sq Mod 8
            Select Case a
                Case 1 ' pawns: centre pawns like advancing; rook pawns should stay home
                    If p > 0 Then adv = r - 1 Else adv = 6 - r
                    If f >= 2 And f <= 5 Then
                        v = v + 3 * adv '        c/d/e/f pawns fight for the middle
                    ElseIf f = 0 Or f = 7 Then
                        v = v - 3 * adv '        a5/h5 style rim lunges cost a little
                    End If
                    v = v + 2 * Ctr(sq)
                    If endgame Then v = v + 3 * adv
                    isolated = -1
                    If f > 0 Then
                        If p > 0 And WPF(f - 1) > 0 Then isolated = 0
                        If p < 0 And BPF(f - 1) > 0 Then isolated = 0
                    End If
                    If f < 7 Then
                        If p > 0 And WPF(f + 1) > 0 Then isolated = 0
                        If p < 0 And BPF(f + 1) > 0 Then isolated = 0
                    End If
                    If isolated Then v = v - 12

                    passed = -1
                    For df = -1 To 1
                        nf = f + df
                        If nf >= 0 And nf <= 7 Then
                            If p > 0 Then
                                If BHigh(nf) > r Then passed = 0
                            Else
                                If WLow(nf) < r Then passed = 0
                            End If
                        End If
                    Next
                    If passed Then
                        If p > 0 Then ownRank = r Else ownRank = 7 - r
                        If ownRank >= 1 And ownRank <= 6 Then v = v + PassBonus(ownRank)
                    End If
                Case 2 ' knights love the centre and hate the back rank
                    v = v + 2 * Ctr(sq)
                    If (p > 0 And r > 0) Or (p < 0 And r < 7) Then v = v + 10
                Case 3 ' bishops mildly central, and want developing too
                    v = v + Ctr(sq)
                    If (p > 0 And r > 0) Or (p < 0 And r < 7) Then v = v + 10
                    light = ((r + f) Mod 2 = 0)
                    If p > 0 Then
                        If light Then wLight = wLight + 1 Else wDark = wDark + 1
                    Else
                        If light Then bLight = bLight + 1 Else bDark = bDark + 1
                    End If
                Case 4
                    If WPF(f) = 0 And BPF(f) = 0 Then
                        v = v + 15
                    ElseIf (p > 0 And WPF(f) = 0) Or (p < 0 And BPF(f) = 0) Then
                        v = v + 8
                    End If
                    If (p > 0 And r = 6) Or (p < 0 And r = 1) Then v = v + 20
                Case 5 ' discourage very early queen sorties
                    If MoveCount < 16 Then
                        If (p > 0 And r > 1) Or (p < 0 And r < 6) Then v = v - 12
                    End If
                Case 6
                    If endgame Then
                        v = v + 3 * Ctr(sq)
                    Else
                        v = v - 2 * Ctr(sq)
                        If p > 0 And (sq = 6 Or sq = 2) Then v = v + 12
                        If p < 0 And (sq = 62 Or sq = 58) Then v = v + 12
                    End If
            End Select
            If p > 0 Then s = s + v Else s = s - v
        End If
    Next
    For f = 0 To 7
        If WPF(f) > 1 Then s = s - 10 * (WPF(f) - 1)
        If BPF(f) > 1 Then s = s + 10 * (BPF(f) - 1)
    Next
    If wLight > 0 And wDark > 0 Then s = s + 15
    If bLight > 0 And bDark > 0 Then s = s - 15
    Evaluate& = s
End Function

' ----- search -------------------------------------------------------------
Function SearchElapsed!
    e! = Timer - SearchStart
    If e! < 0 Then e! = e! + 86400
    SearchElapsed! = e!
End Function

Sub PollSearch
    If StopSearch Then Exit Sub
    If TimeBudget > 0 Then
        If SearchElapsed! >= TimeBudget Then
            StopSearch = -1: StopMode = 1: StopReason$ = "time limit"
            Exit Sub
        End If
    End If
    If (Nodes And 1023) = 0 Then
        k$ = InKey$
        If k$ = " " Then
            StopSearch = -1: StopMode = 1: StopReason$ = "SPACE"
        ElseIf k$ = Chr$(27) Then
            StopSearch = -1: StopMode = 2: StopReason$ = "ESC"
        End If
    End If
End Sub

Function SearchRepetition (ply)
    n = 1
    For i = 1 To GameTop
        If GHash(i) = PosHash Then n = n + 1
    Next
    For i = 0 To ply - 1
        If HashLine(i) = PosHash Then n = n + 1
    Next
    If n >= 3 Then SearchRepetition = -1
End Function

Sub SetPVFromMove (ply, f0, t0, pr)
    PVF(ply, 0) = f0: PVT(ply, 0) = t0: PVP(ply, 0) = pr
    For j = 0 To PVLen(ply + 1) - 1
        PVF(ply, j + 1) = PVF(ply + 1, j)
        PVT(ply, j + 1) = PVT(ply + 1, j)
        PVP(ply, j + 1) = PVP(ply + 1, j)
    Next
    PVLen(ply) = PVLen(ply + 1) + 1
End Sub

' Quiescence searches every legal evasion in check, otherwise only noisy moves.
Function Quiesce& (al&, be&, ply)
    If StopSearch Then Quiesce& = al&: Exit Function
    Nodes = Nodes + 1
    PollSearch
    If StopSearch Then Quiesce& = al&: Exit Function
    If HalfClock >= 100 Or SearchRepetition(ply) Or InsufficientMaterial Then Quiesce& = 0: Exit Function
    PVLen(ply) = 0
    inchk = InCheckNow
    st& = Stm * Evaluate&
    a& = al&
    If inchk = 0 Then
        If st& >= be& Then Quiesce& = st&: Exit Function
        If st& > a& Then a& = st&
    End If
    If ply >= MAXPLY - 1 Then
        If inchk Then Quiesce& = st& Else Quiesce& = a&
        Exit Function
    End If
    Gen ply
    If inchk Then last = NM(ply) Else last = NC(ply)
    legal = 0
    For i = 1 To last
        If StopSearch Then Quiesce& = a&: Exit Function
        victim = Abs(B(MT(ply, i)))
        If victim = 0 And Abs(B(MF(ply, i))) = 1 And MT(ply, i) = EpSq Then victim = 1
        skipMove = 0
        If inchk = 0 And victim > 0 Then
            If st& + MatVal(victim) + 200 < a& Then skipMove = -1
        End If
        If skipMove = 0 Then
            f0 = MF(ply, i): t0 = MT(ply, i): pr = MP(ply, i)
            MakeMove ply, i
            If Bad Then
                UnMake ply, i
            Else
                legal = legal + 1
                HashLine(ply + 1) = PosHash
                s& = -Quiesce&(-be&, -a&, ply + 1)
                UnMake ply, i
                If StopSearch Then Quiesce& = a&: Exit Function
                If s& > a& Then
                    a& = s&
                    SetPVFromMove ply, f0, t0, pr
                    If a& >= be& Then Quiesce& = a&: Exit Function
                End If
            End If
        End If
    Next
    If inchk And legal = 0 Then Quiesce& = -MATE + ply Else Quiesce& = a&
End Function

Function Search& (dep, al&, be&, ply, ext)
    If StopSearch Then Search& = al&: Exit Function
    Nodes = Nodes + 1
    PollSearch
    If StopSearch Then Search& = al&: Exit Function
    If HalfClock >= 100 Or SearchRepetition(ply) Or InsufficientMaterial Then Search& = 0: Exit Function
    PVLen(ply) = 0
    inchk = InCheckNow
    ' Work on locals: QB64 parameters are ByRef, so mutating ext here would
    ' leak a child's extension count into later sibling branches.
    workDep = dep: nextExt = ext
    If inchk And nextExt < 4 Then workDep = workDep + 1: nextExt = nextExt + 1
    If workDep <= 0 Then Search& = Quiesce&(al&, be&, ply): Exit Function

    origAlpha& = al&
    ti& = PosHash And (TTSIZE - 1)
    ttCode& = 0
    If TTKey(ti&) = PosHash Then
        ttCode& = TTMove(ti&)
        If TTDepth(ti&) >= workDep Then
            ts& = TTScore(ti&)
            If TTFlag(ti&) = 0 Then
                If ttCode& Then
                    DecodeMove ttCode&, f0, t0, pr
                    PVF(ply, 0) = f0: PVT(ply, 0) = t0: PVP(ply, 0) = pr: PVLen(ply) = 1
                End If
                Search& = ts&: Exit Function
            End If
            If TTFlag(ti&) = 1 And ts& <= al& Then Search& = ts&: Exit Function
            If TTFlag(ti&) = 2 And ts& >= be& Then Search& = ts&: Exit Function
        End If
    End If

    Gen ply
    If ttCode& Then
        DecodeMove ttCode&, tf, tt, tp
        noisy = (B(tt) <> 0 Or tp <> 0)
        If Abs(B(tf)) = 1 And tt = EpSq And (tf Mod 8) <> (tt Mod 8) Then noisy = -1
        If noisy Then target = 1 Else target = NC(ply) + 1
        BringMove ply, tf, tt, tp, target
    End If
    a& = al&
    legal = 0: bestCode& = 0
    For i = 1 To NM(ply)
        If StopSearch Then Search& = a&: Exit Function
        quiet = (i > NC(ply))
        f0 = MF(ply, i): t0 = MT(ply, i): pr = MP(ply, i)
        MakeMove ply, i
        If Bad Then
            UnMake ply, i
        Else
            legal = legal + 1
            HashLine(ply + 1) = PosHash
            s& = -Search&(workDep - 1, -be&, -a&, ply + 1, nextExt)
            UnMake ply, i
            If StopSearch Then Search& = a&: Exit Function
            If s& > a& Then
                a& = s&: bestCode& = MoveCode&(f0, t0, pr)
                SetPVFromMove ply, f0, t0, pr
                If a& >= be& Then
                    If quiet Then
                        If KillerMv(ply, 0) <> bestCode& Then
                            KillerMv(ply, 1) = KillerMv(ply, 0): KillerMv(ply, 0) = bestCode&
                        End If
                    End If
                    TTKey(ti&) = PosHash: TTDepth(ti&) = workDep: TTScore(ti&) = a&
                    TTFlag(ti&) = 2: TTMove(ti&) = bestCode&
                    Search& = a&: Exit Function
                End If
            End If
        End If
    Next
    If legal = 0 Then
        If inchk Then a& = -MATE + ply Else a& = 0
    End If
    TTKey(ti&) = PosHash: TTDepth(ti&) = workDep: TTScore(ti&) = a&: TTMove(ti&) = bestCode&
    If a& <= origAlpha& Then TTFlag(ti&) = 1 Else TTFlag(ti&) = 0
    Search& = a&
End Function

Function ScoreStr$ (sc&)
    If sc& > MATE - 100 Then
        ScoreStr$ = "mate in" + Str$((MATE - sc& + 1) \ 2)
    ElseIf sc& < -(MATE - 100) Then
        ScoreStr$ = "mated in" + Str$((MATE + sc& + 1) \ 2)
    ElseIf sc& >= 0 Then
        ScoreStr$ = "+" + LTrim$(Str$(sc&)) + " cp"
    Else
        ScoreStr$ = LTrim$(Str$(sc&)) + " cp"
    End If
End Function

' ----- root iterative deepening, shared by engine play and hint ------------
Sub RunSearch (limitDepth)
    Dim best As Long, s As Long
    SearchBestF = -1: SearchBestT = -1: SearchBestP = 0
    SearchScore = 0: SearchDepthDone = 0: SearchPV$ = ""
    StopSearch = 0: StopMode = 0: StopReason$ = ""
    Nodes = 0: SearchStart = Timer: Thinking = -1
    es = Stm
    HashLine(0) = PosHash
    prevF = -1: prevT = -1: prevP = 0
    fallbackF = -1: fallbackT = -1: fallbackP = 0
    Gen 0
    For i = 1 To NM(0)
        MakeMove 0, i
        bd = Bad
        UnMake 0, i
        If bd = 0 Then
            fallbackF = MF(0, i): fallbackT = MT(0, i): fallbackP = MP(0, i)
            Exit For
        End If
    Next
    UiAnalysis$ = "Starting iterative-deepening search."
    DrawGameScreen

    For d = 1 To limitDepth
        If d > 1 And TimeBudget > 0 Then
            If SearchElapsed! >= TimeBudget * .4 Then
                StopReason$ = "time reserve"
                Exit For
            End If
        End If
        Gen 0
        If prevF >= 0 Then BringMove 0, prevF, prevT, prevP, 1
        best = -INF: iterF = -1: iterT = -1: iterP = 0: iterPV$ = ""
        legal = 0
        For i = 1 To NM(0)
            If TimeBudget > 0 And SearchElapsed! >= TimeBudget Then
                StopSearch = -1: StopMode = 1: StopReason$ = "time limit"
            End If
            k$ = InKey$
            If k$ = " " Then StopSearch = -1: StopMode = 1: StopReason$ = "SPACE"
            If k$ = Chr$(27) Then StopSearch = -1: StopMode = 2: StopReason$ = "ESC"
            If StopSearch Then Exit For
            f0 = MF(0, i): t0 = MT(0, i): pr = MP(0, i)
            MakeMove 0, i
            If Bad Then
                UnMake 0, i
            Else
                legal = legal + 1
                HashLine(1) = PosHash
                PVLen(1) = 0
                s = -Search&(d - 1, -INF, -best, 1, 0)
                UnMake 0, i
                If StopSearch Then Exit For
                If s > best Then
                    best = s: iterF = f0: iterT = t0: iterP = pr
                    iterPV$ = MoveText$(f0, t0, pr)
                    For j = 0 To PVLen(1) - 1
                        iterPV$ = iterPV$ + " " + MoveText$(PVF(1, j), PVT(1, j), PVP(1, j))
                    Next
                End If
            End If
        Next
        If StopSearch Then Exit For
        If legal = 0 Or iterF < 0 Then Exit For
        SearchBestF = iterF: SearchBestT = iterT: SearchBestP = iterP
        SearchScore = best: SearchDepthDone = d: SearchPV$ = iterPV$
        prevF = iterF: prevT = iterT: prevP = iterP
        elapsed! = SearchElapsed!
        UiAnalysis$ = "Depth " + LTrim$(Str$(d)) + ": PV " + SearchPV$ + "  " + ScoreStr$(es * best)
        UiAnalysis$ = UiAnalysis$ + "  |  " + LTrim$(Str$(Nodes)) + " nodes  |  "
        UiAnalysis$ = UiAnalysis$ + LTrim$(Str$(Int(elapsed! * 10) / 10)) + " s"
        DrawGameScreen
    Next
    Thinking = 0
    If StopMode = 1 And SearchBestF < 0 And fallbackF >= 0 Then
        SearchBestF = fallbackF: SearchBestT = fallbackT: SearchBestP = fallbackP
        SearchScore = 0: SearchPV$ = MoveText$(fallbackF, fallbackT, fallbackP)
    End If
    If StopReason$ <> "" Then
        UiAnalysis$ = "Search stopped at depth " + LTrim$(Str$(SearchDepthDone))
        UiAnalysis$ = UiAnalysis$ + " (" + StopReason$ + ")."
        If SearchPV$ <> "" Then UiAnalysis$ = UiAnalysis$ + " PV " + SearchPV$
    End If
End Sub

Sub HintMove
    UiMessage$ = "Calculating a hint..."
    RunSearch 3
    If StopMode = 2 Then
        UiMessage$ = "Hint search canceled; the position is unchanged."
    ElseIf SearchBestF >= 0 Then
        san$ = MakeSan$(SearchBestF, SearchBestT, SearchBestP)
        UiMessage$ = "Hint: " + san$ + " (" + MoveText$(SearchBestF, SearchBestT, SearchBestP) + ")."
    Else
        UiMessage$ = "No hint is available."
    End If
End Sub

Sub EngineMove
    ' A random sound first move for either side; invalid entries fall through.
    bk$ = ""
    If MoveCount = 0 And Stm = 1 Then
        Select Case Int(Rnd * 6)
            Case 0: bk$ = "d2d4"
            Case 1: bk$ = "e2e4"
            Case 2: bk$ = "c2c4"
            Case 3: bk$ = "g1f3"
            Case 4: bk$ = "b1c3"
            Case 5: bk$ = "g2g3"
        End Select
    ElseIf MoveCount = 1 And Stm = -1 Then
        Select Case Int(Rnd * 4)
            Case 0: bk$ = "e7e6"
            Case 1: bk$ = "d7d5"
            Case 2: bk$ = "g8f6"
            Case 3: bk$ = "c7c5"
        End Select
    End If
    If bk$ <> "" Then
        If DoMove(bk$) Then
            UiAnalysis$ = "Opening book: chose " + bk$ + " at random from a small sound-move list."
            Exit Sub
        End If
    End If

    es = Stm
    UiMessage$ = "Engine is thinking for " + SideName$(Stm) + "..."
    RunSearch MaxDepth
    If StopMode = 2 Then
        EnginePaused = -1
        UiMessage$ = "Search canceled with ESC; position unchanged. Type go to resume the engine."
        Exit Sub
    End If
    If SearchBestF < 0 Then
        UiMessage$ = "Engine search ended without a completed legal move."
        Exit Sub
    End If

    If SearchScore < -900 Then EngineBadCount = EngineBadCount + 1 Else EngineBadCount = 0
    If EngineBadCount >= 3 Then
        GameEnded = -1: GameReason$ = "resignation"
        If es = 1 Then GameResult$ = "0-1" Else GameResult$ = "1-0"
        UiMessage$ = SideName$(es) + " engine resigns."
        Exit Sub
    End If

    f0 = SearchBestF: t0 = SearchBestT: pr = SearchBestP
    san$ = MakeSan$(f0, t0, pr)
    CommitMove f0, t0, pr, es, san$
    If GameEnded = 0 Then UiMessage$ = SideName$(es) + " played " + san$ + "."
End Sub

' ----- human move entry ---------------------------------------------------
Function DoMove (raw$)
    DoMove = 0
    s$ = ""
    For i = 1 To Len(raw$) ' strip decoration from supported long algebraic input
        c$ = Mid$(LCase$(raw$), i, 1)
        If InStr(" x+#=-", c$) = 0 Then s$ = s$ + c$
    Next
    frm = -1: dst = -1: pr = 0
    If s$ = "oo" Or s$ = "00" Then
        If Stm = 1 Then frm = 4: dst = 6 Else frm = 60: dst = 62
    ElseIf s$ = "ooo" Or s$ = "000" Then
        If Stm = 1 Then frm = 4: dst = 2 Else frm = 60: dst = 58
    Else
        If Len(s$) < 4 Or Len(s$) > 5 Then UiMessage$ = "Bad move format - type 'help' for examples.": Exit Function
        f1 = Asc(Mid$(s$, 1, 1)) - 97: r1 = Asc(Mid$(s$, 2, 1)) - 49
        f2 = Asc(Mid$(s$, 3, 1)) - 97: r2 = Asc(Mid$(s$, 4, 1)) - 49
        If f1 < 0 Or f1 > 7 Or r1 < 0 Or r1 > 7 Or f2 < 0 Or f2 > 7 Or r2 < 0 Or r2 > 7 Then
            UiMessage$ = "Bad squares - files must be a-h and ranks must be 1-8.": Exit Function
        End If
        frm = r1 * 8 + f1: dst = r2 * 8 + f2
        If Len(s$) = 5 Then
            pr = InStr(" pnbrq", Mid$(s$, 5, 1)) - 1
            If pr < 2 Then UiMessage$ = "Promotion letter must be q, r, b or n.": Exit Function
        End If
    End If
    Gen 0
    For i = 1 To NM(0)
        If MF(0, i) = frm And MT(0, i) = dst Then
            ok = 0
            If MP(0, i) = 0 And pr = 0 Then ok = 1
            If MP(0, i) > 0 And pr = MP(0, i) Then ok = 1
            If MP(0, i) = 5 And pr = 0 Then ok = 1 ' promotion with no letter = queen
            If ok Then
                movingSide = Stm
                MakeMove 0, i
                If Bad Then
                    UnMake 0, i
                    UiMessage$ = "Illegal move - your king would be in check."
                    Exit Function
                End If
                realPr = MP(0, i)
                UnMake 0, i
                san$ = MakeSan$(frm, dst, realPr)
                CommitMove frm, dst, realPr, movingSide, san$
                If GameEnded = 0 Then UiMessage$ = SideName$(movingSide) + " played " + san$ + "."
                DoMove = 1
                Exit Function
            End If
        End If
    Next
    UiMessage$ = "That is not a legal move in this position."
End Function

