' ==========================================================================
'  COOL CHESS 1.2  -  a lean chess engine with a self-contained board UI
'  v1.2: full en passant support in move generation, search, make/unmake,
'        capture tracking and human move entry.
'  v1.1: pixel-art piece set (auto outline + drop shadow), UI polish,
'        opening eval terms and a tiny randomized 1-move opening book.
' ==========================================================================
'  Board: 64 ints, a1=0 ... h8=63.  Pieces: 1=P 2=N 3=B 4=R 5=Q 6=K.
'  Positive = White, negative = Black, 0 = empty.
'  Search:  negamax alpha-beta + capture/promotion quiescence,
'           iterative deepening with previous-best-first ordering.
'  Eval:    material + a few tiny positional terms (see Evaluate&).
'
'  DESIGNED FOR LATER EXPANSION - hooks already in place:
'    * EpSq is tracked/saved/restored on every make/unmake. En passant
'      is fully supported by both the human player and engine search.
'    * Evaluate& is one self-contained function - add mobility, pawn
'      structure, king safety etc. there without touching the search.
'    * Repetition / 50-move draws: add a history array in MakeMove.
' ==========================================================================
DefInt A-Z

Const MAXPLY = 40 '  max search ply including quiescence
Const MAXMV = 220 '  max moves in one position
Const INF = 2000000
Const MATE = 1000000

Dim Shared B(63) '                board
Dim Shared Stm, CR, EpSq '        side to move (1/-1), castle rights bits (1=WK 2=WQ 4=BK 8=BQ), ep square (-1 = none)
Dim Shared WK, BK '               king squares
Dim Shared HumanSide, ViewSide, MaxDepth
Dim Shared LastFrom, LastTo, LastPromo, MoveCount, Thinking
Dim Shared MoveHistory$(512)
Dim Shared UiMessage$, UiAnalysis$, WhiteCaptures$, BlackCaptures$
Dim Shared MF(MAXPLY, MAXMV), MT(MAXPLY, MAXMV), MP(MAXPLY, MAXMV) ' move lists per ply: from, to, promo piece
Dim Shared NM(MAXPLY), NC(MAXPLY) ' move count / noisy (capture+promo) count per ply; noisy moves sit at the front
Dim Shared UCap(MAXPLY), UCR(MAXPLY), UPc(MAXPLY), UEp(MAXPLY) '     undo info per ply
Dim Shared Nodes As Long
Dim Shared MatVal(6), Ctr(63)
Dim Shared KN(7, 1), KG(7, 1) '   knight offsets; king/slider dirs (0-3 straight, 4-7 diagonal)
Dim Shared SPR(6, 25, 21) '       22x26 piece sprites: 0 empty, 1 body, 2 inked detail

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
Randomize Timer '                 for the little opening book

Screen _NewImage(1060, 660, 32)
_Title "Cool Chess"
_Font 16
_PrintMode _KeepBackground
MaxDepth = 5
HumanSide = 1
ViewSide = 1
InitGame
UiMessage$ = "New game. You are White. Enter a move such as e2e4."

' ----- main loop -----
Do
    over = 0
    If AnyLegal = 0 Then
        If InCheckNow Then
            If Stm = 1 Then UiMessage$ = "CHECKMATE - Black wins." Else UiMessage$ = "CHECKMATE - White wins."
        Else
            UiMessage$ = "STALEMATE - draw."
        End If
        over = 1
    End If

    DrawGameScreen
    If over = 0 And Stm <> HumanSide Then
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
                Else
                    HumanSide = -Stm
                    ViewSide = HumanSide
                    UiMessage$ = "The engine will play " + SideName$(Stm) + "; you are now " + SideName$(HumanSide) + "."
                End If
            Case Else
                If over Then
                    UiMessage$ = "Game over - type 'new' or 'quit'."
                ElseIf Left$(c$, 6) = "depth " Then
                    n = Val(Mid$(c$, 7))
                    If n >= 1 And n <= 8 Then
                        MaxDepth = n
                        UiMessage$ = "Search depth set to " + LTrim$(Str$(n)) + "."
                    Else
                        UiMessage$ = "Depth must be from 1 through 8."
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
Data "........XXXXXX........"
Data ".......XXXXXXXX......."
Data ".......XXXXXXXX......."
Data ".......XXXXXXXX......."
Data "........XXXXXX........"
Data "......XXXXXXXXXX......"
Data "........XXXXXX........"
Data "........XXXXXX........"
Data "........XXXXXX........"
Data ".......XXXXXXXX......."
Data ".......XXXXXXXX......."
Data "......XXXXXXXXXX......"
Data "......XXXXXXXXXX......"
Data ".....XXXXXXXXXXXX....."
Data ".....XXXXXXXXXXXX....."
Data "....XXXXXXXXXXXXXX...."
Data "...XXXXXXXXXXXXXXXX..."
Data "......................"
Data "...XXXXXXXXXXXXXXXX..."
Data "..XXXXXXXXXXXXXXXXXX.."
Data "..XXXXXXXXXXXXXXXXXX.."
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
    MoveCount = 0: Thinking = 0
    UiAnalysis$ = "": WhiteCaptures$ = "": BlackCaptures$ = ""
End Sub

Sub ShowHelp
    _Display
    Cls , _RGB32(18, 21, 26)
    _PrintMode _KeepBackground
    Color _RGB32(236, 202, 116)
    _PrintString (42, 26), "COOL CHESS HELP"
    Color _RGB32(226, 229, 235)
    _PrintString (42, 58), "MOVE FORMAT - coordinate algebraic notation"
    _PrintString (62, 84), "From-square followed by to-square:  e2e4   g8f6   a7a5"
    _PrintString (62, 108), "Files are a-h and ranks are 1-8.  e2e4 moves the piece on e2 to e4."
    _PrintString (62, 132), "Decoration is optional: e2-e4, exd5 and e4+ are accepted."
    _PrintString (62, 156), "Promotion: e7e8q (q, r, b or n). Omitting the letter promotes to queen."
    _PrintString (62, 180), "Castling: e1g1 / e1c1 / e8g8 / e8c8, or enter o-o / o-o-o."
    Color _RGB32(236, 202, 116)
    _PrintString (42, 218), "COMMANDS"
    Color _RGB32(226, 229, 235)
    _PrintString (62, 244), "go         Engine plays the side to move; you take the other side."
    _PrintString (62, 268), "depth n    Search depth 1-8. Higher is stronger and slower."
    _PrintString (62, 292), "flip       Turn the board around without changing which side you play."
    _PrintString (62, 316), "eval       Show a static evaluation (positive favors White)."
    _PrintString (62, 340), "new        Start a new game as White."
    _PrintString (62, 364), "board / d  Refresh.     help / h  This screen.     quit / q  Exit."
    Color _RGB32(174, 181, 194)
    _PrintString (42, 410), "White pieces are ivory; Black pieces are charcoal. The latest move is gold."
    _PrintString (42, 434), "The board automatically turns so your side is at the bottom."
    _PrintString (42, 458), "Engine notes: en passant is automatic; enter it as a normal diagonal pawn move."
    _PrintString (42, 482), "The engine's first move for either side comes from a small randomized opening book."
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

Sub RecordMove (m$)
    If MoveCount < 512 Then
        MoveCount = MoveCount + 1
        MoveHistory$(MoveCount) = m$
    End If
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
    _PrintString (34, 20), "COOL CHESS 1.1"
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
            If ring~& <> 0 Then
                Line (x, y)-(x + ss - 1, y + ss - 1), ring~&, B
                Line (x + 1, y + 1)-(x + ss - 2, y + ss - 2), ring~&, B
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
    _PrintString (px + 260, py + 40), "Depth: " + LTrim$(Str$(MaxDepth))
    If MoveCount > 0 Then
        _PrintString (px + 260, py + 60), "Last: " + MoveHistory$(MoveCount)
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
            If wi <= MoveCount Then histLine$ = histLine$ + MoveHistory$(wi)
            If bi <= MoveCount Then histLine$ = histLine$ + Space$(8 - Len(MoveHistory$(wi))) + MoveHistory$(bi)
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
    _PrintString (34, 547), "Move: e2e4     Promotion: e7e8q     Castling: o-o / o-o-o"
    Color _RGB32(164, 172, 188)
    _PrintString (34, 566), "Commands: help   new   go   flip   depth 1-8   eval   quit"

    Line (20, 592)-(1040, 638), _RGB32(11, 14, 18), BF
    Line (20, 592)-(1040, 638), _RGB32(102, 113, 132), B
    _Display
    _AutoDisplay
End Sub

Sub GetCommand (c$, over)
    _PrintMode _FillBackground
    Color _RGB32(240, 243, 248), _RGB32(11, 14, 18)
    Locate 39, 4
    If over Then
        Print "Game over > ";
    ElseIf Stm = 1 Then
        Print "White move > ";
    Else
        Print "Black move > ";
    End If
    Line Input c$
    _PrintMode _KeepBackground
End Sub

Function Sq2$ (sq)
    Sq2$ = Chr$(97 + (sq Mod 8)) + Chr$(49 + (sq \ 8))
End Function

Function MvStr$ (ply, i)
    m$ = Sq2$(MF(ply, i)) + Sq2$(MT(ply, i))
    If MP(ply, i) Then m$ = m$ + Mid$(" pnbrq", MP(ply, i) + 1, 1)
    MvStr$ = m$
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
    ' En passant: a pawn moves diagonally to the empty EpSq and removes
    ' the enemy pawn from the square it just passed to.
    If Abs(p) = 1 And t0 = EpSq And B(t0) = 0 Then
        If (f0 Mod 8) <> (t0 Mod 8) Then B(t0 - 8 * Stm) = 0
    End If
    B(t0) = p: B(f0) = 0
    If pr Then B(t0) = pr * Stm
    If p = 6 Then WK = t0
    If p = -6 Then BK = t0
    If Abs(p) = 6 Then ' castling: move the rook too
        If t0 - f0 = 2 Then B(t0 - 1) = B(t0 + 1): B(t0 + 1) = 0
        If f0 - t0 = 2 Then B(t0 + 1) = B(t0 - 2): B(t0 - 2) = 0
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
    Stm = -Stm
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
    s = 0
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
                Case 2 ' knights love the centre and hate the back rank
                    v = v + 2 * Ctr(sq)
                    If (p > 0 And r > 0) Or (p < 0 And r < 7) Then v = v + 10
                Case 3 ' bishops mildly central, and want developing too
                    v = v + Ctr(sq)
                    If (p > 0 And r > 0) Or (p < 0 And r < 7) Then v = v + 10
                Case 5 ' discourage very early queen sorties
                    If MoveCount < 16 Then
                        If (p > 0 And r > 1) Or (p < 0 And r < 6) Then v = v - 12
                    End If
                Case 6 ' keep the king out of the middle; reward the castled corners
                    v = v - 2 * Ctr(sq)
                    If p > 0 And (sq = 6 Or sq = 2) Then v = v + 12
                    If p < 0 And (sq = 62 Or sq = 58) Then v = v + 12
            End Select
            If p > 0 Then s = s + v Else s = s - v
        End If
    Next
    ' TODO: mobility, doubled/isolated/passed pawns, rooks on open files,
    '       bishop pair, real king safety, endgame king activity
    Evaluate& = s
End Function

' ----- search -------------------------------------------------------------
' Quiescence: only look at captures/promotions so the eval is never taken
' in the middle of a piece trade (prevents gross horizon blunders).
Function Quiesce& (al&, be&, ply)
    Nodes = Nodes + 1
    st& = Stm * Evaluate&
    If st& >= be& Then Quiesce& = st&: Exit Function
    a& = al&
    If st& > a& Then a& = st&
    If ply >= MAXPLY - 1 Then Quiesce& = a&: Exit Function
    Gen ply
    For i = 1 To NC(ply) ' noisy moves only - they sit at the front of the list
        MakeMove ply, i
        If Bad Then
            UnMake ply, i
        Else
            s& = -Quiesce&(-be&, -a&, ply + 1)
            UnMake ply, i
            If s& > a& Then
                a& = s&
                If a& >= be& Then Quiesce& = a&: Exit Function
            End If
        End If
    Next
    Quiesce& = a&
End Function

Function Search& (dep, al&, be&, ply)
    If dep <= 0 Then Search& = Quiesce&(al&, be&, ply): Exit Function
    Nodes = Nodes + 1
    Gen ply
    a& = al&
    legal = 0
    For i = 1 To NM(ply)
        MakeMove ply, i
        If Bad Then
            UnMake ply, i
        Else
            legal = legal + 1
            s& = -Search&(dep - 1, -be&, -a&, ply + 1)
            UnMake ply, i
            If s& > a& Then
                a& = s&
                If a& >= be& Then Search& = a&: Exit Function ' beta cutoff
            End If
        End If
    Next
    If legal = 0 Then ' no legal moves: mate (prefer faster mates) or stalemate
        If InCheckNow Then Search& = -MATE + ply Else Search& = 0
    Else
        Search& = a&
    End If
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

' ----- root: iterative deepening with compact on-screen thinking display ---
Sub EngineMove
    Dim best As Long, s As Long
    ' ----- tiny opening book: a random sound first move for either side ----
    ' DoMove validates against the real move generator, so if a book move
    ' were ever illegal we simply fall through to the normal search.
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
            UiAnalysis$ = "Opening book: chose " + bk$ + " at random from a small list of sound first moves."
            Exit Sub
        End If
    End If
    t! = Timer
    Nodes = 0
    es = Stm ' engine side; all displayed scores converted to White's view
    Thinking = 1
    UiMessage$ = "Engine is thinking for " + SideName$(Stm) + "..."
    UiAnalysis$ = "Starting iterative-deepening search."
    DrawGameScreen
    bf = -1: bt = -1: bp = 0: bi = 0
    For d = 1 To MaxDepth
        Gen 0
        If bf >= 0 Then ' search last iteration's best move first - big pruning win
            For i = 2 To NM(0)
                If MF(0, i) = bf And MT(0, i) = bt And MP(0, i) = bp Then
                    Swap MF(0, 1), MF(0, i)
                    Swap MT(0, 1), MT(0, i)
                    Swap MP(0, 1), MP(0, i)
                    Exit For
                End If
            Next
        End If
        best = -INF: bi = 0
        For i = 1 To NM(0)
            MakeMove 0, i
            If Bad Then
                UnMake 0, i
            Else
                s = -Search&(d - 1, -INF, -best, 1)
                UnMake 0, i
                isnew = 0
                If s > best Then isnew = 1
                If isnew Then
                    best = s: bi = i
                    bf = MF(0, i): bt = MT(0, i): bp = MP(0, i)
                End If
            End If
        Next
        elapsed! = Timer - t!
        If elapsed! < 0 Then elapsed! = elapsed! + 86400
        UiAnalysis$ = "Depth " + LTrim$(Str$(d)) + ": " + MvStr$(0, bi) + "  " + ScoreStr$(es * best)
        UiAnalysis$ = UiAnalysis$ + "  |  " + LTrim$(Str$(Nodes)) + " nodes  |  "
        UiAnalysis$ = UiAnalysis$ + LTrim$(Str$(Int(elapsed! * 10) / 10)) + " s"
        DrawGameScreen
    Next
    m$ = MvStr$(0, bi)
    captured = B(MT(0, bi))
    If Abs(B(MF(0, bi))) = 1 And MT(0, bi) = EpSq And captured = 0 Then captured = -es
    LastFrom = MF(0, bi): LastTo = MT(0, bi): LastPromo = MP(0, bi)
    RecordMove m$
    RecordCapture captured, es
    MakeMove 0, bi
    Thinking = 0
    UiMessage$ = SideName$(es) + " played " + m$ + "."
    If InCheckNow Then UiMessage$ = UiMessage$ + " Check."
End Sub

' ----- human move entry ---------------------------------------------------
Function DoMove (raw$)
    DoMove = 0
    s$ = ""
    For i = 1 To Len(raw$) ' strip decoration so e2-e4, exd5, e4+ etc. still parse
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
                m$ = MvStr$(0, i)
                movingSide = Stm
                captured = B(dst)
                If Abs(B(frm)) = 1 And dst = EpSq And captured = 0 Then captured = -movingSide
                MakeMove 0, i
                If Bad Then
                    UnMake 0, i
                    UiMessage$ = "Illegal move - your king would be in check."
                    Exit Function
                End If
                LastFrom = frm: LastTo = dst: LastPromo = MP(0, i)
                RecordMove m$
                RecordCapture captured, movingSide
                UiMessage$ = SideName$(movingSide) + " played " + m$ + "."
                If InCheckNow Then UiMessage$ = UiMessage$ + " Check."
                DoMove = 1
                Exit Function
            End If
        End If
    Next
    UiMessage$ = "That is not a legal move in this position."
End Function


