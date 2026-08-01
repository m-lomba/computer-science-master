import sys
import subprocess
import time
import io

QWORD_30A0_RAW = [
    -6557166050133734912, 20635638558755360, 2990706916155597072, 1316230460770091648,
    -4224278778085112704, -9151278695688156904, 6363695179958992897, 42499150490648612,
    78883380612432904, 594633480929809441, 576743358756629084, 5909989967199355164,
    5827663020977308144, 5764893671640268961, -8502742694855567287, 18015637081174036,
    -6700070227946891248, 352686205833988, 5309762317376946723, 2603091721552137233,
    -8894595470489416702, 1046670758958400564, 36552722899550336, 1747424195303777848,
    1522499352961124160, 4574605654164737, 720649609168609328, 2886579138463252,
    -6842654043436677629, 5765241396890976576, 2442339337623306284, -9222235403489115516,
    -5473877948150542319, -9185775525233012144, 288279476956083200, 576777755250409992,
    6070857383494829568, 4758124509024758284, 2605403307398791168, 2395950186268050699,
    -8641281784882908146, -6444272284473490352, 2449958687209570304, 5644535210016,
    6918690661687230532, 375223739371102503, -8609576095634092026, 41968442617714201,
    -8574690954177411520, 342486467170390057, 2251843372089378, 4756367062008072336,
    4629788863770181658, 1008817451651309608, 662618663870007301, 6993281262152583556,
    5485468052911239168, -9130907366318368768, 4620742202540195844, 4625356247674178701,
    -8619254164754463488, 422385409360000, 289391755190599808, 3378353512990464
]
QWORD_30A0 = [v & 0xFFFFFFFFFFFFFFFF for v in QWORD_30A0_RAW]

SPIRAL_DX = [1,1,0,-1,-1,-1,0,1,2,2,2,2,1,0,-1,-2,-2,-2,-2,-2,-1,0,1,2,
             3,3,3,3,3,3,2,1,0,-1,-2,-3,-3,-3,-3,-3,-3,-3,-2,-1,0,1,2,3,
             4,4,4,4,4,4,4,4,3,2,1,0,-1,-2,-3,-4]

SPIRAL_DY = [0,1,1,1,0,-1,-1,-1,-1,0,1,2,2,2,2,2,1,0,-1,-2,-2,-2,-2,-2,
             -2,-1,0,1,2,3,3,3,3,3,3,3,2,1,0,-1,-2,-3,-3,-3,-3,-3,-3,-3,
             -3,-2,-1,0,1,2,3,4,4,4,4,4,4,4,4,4]

J_MOVES = [(3,1),(3,-1),(-3,1),(-3,-1),(1,3),(1,-3),(-1,3),(-1,-3)]

CHAR_TO_BYTE = {'.':0,'K':1,'V':2,'S':3,'J':4,'M':5,
                'k':9,'v':10,'s':11,'j':12,'m':13}
BYTE_TO_CHAR = {v:k for k,v in CHAR_TO_BYTE.items()}

def in_bounds(x, y):
    return 0 <= x < 8 and 0 <= y < 8

def apply_move(board, fx, fy, tx, ty):
    """Ritorna una NUOVA board dopo la mossa (non modifica l'originale)."""
    nb = [row[:] for row in board]
    nb[ty][tx] = nb[fy][fx]
    nb[fy][fx] = 0
    return nb

def find_king(board, black):
    for y in range(8):
        for x in range(8):
            v = board[y][x]
            if (v & 7) == 1 and bool(v & 8) == black:
                return (x, y)
    return None

def get_moves(board, fx, fy):
    piece = board[fy][fx]
    if not piece: return []
    ptype  = piece & 7
    pblack = bool(piece & 8)
    moves  = []

    if ptype == 1: # K
        for dy in range(-1, 2):
            for dx in range(-1, 2):
                if dx == 0 and dy == 0: continue
                tx, ty = fx + dx, fy + dy
                if in_bounds(tx, ty):
                    t = board[ty][tx]
                    if not t or bool(t & 8) != pblack:
                        moves.append((tx, ty))

    elif ptype == 2: # V
        fwd = -1 if pblack else 1
        ty  = fy + fwd
        for dx in [-1, 1]:
            tx = fx + dx
            if in_bounds(tx, ty) and not board[ty][tx]:
                moves.append((tx, ty))
        if in_bounds(fx, ty):
            t = board[ty][fx]
            if t and bool(t & 8) != pblack:
                moves.append((fx, ty))

    elif ptype == 3: # S
        for m in range(63):
            tx = fx + SPIRAL_DX[m]
            ty = fy + SPIRAL_DY[m]
            if not in_bounds(tx, ty): continue
            t = board[ty][tx]
            if t:
                if bool(t & 8) != pblack:
                    moves.append((tx, ty))
                return moves
            moves.append((tx, ty))

    elif ptype == 4: # J
        for dx, dy in J_MOVES:
            tx, ty = fx + dx, fy + dy
            if in_bounds(tx, ty):
                t = board[ty][tx]
                if not t or bool(t & 8) != pblack:
                    moves.append((tx, ty))

    elif ptype == 5: # M
        mask = QWORD_30A0[fy * 8 + fx]
        for i in range(64):
            if (mask >> i) & 1:
                tx, ty = i % 8, i // 8
                if in_bounds(tx, ty):
                    t = board[ty][tx]
                    if not t or bool(t & 8) != pblack:
                        moves.append((tx, ty))

    return moves


def attacks_1941(board, fx, fy, tx, ty):
    piece = board[fy][fx]
    if not piece: return False
    ptype = piece & 7

    if ptype == 1:
        return abs(fx - tx) <= 1 and abs(fy - ty) <= 1 and (fx != tx or fy != ty)
    elif ptype == 2:
        fwd = -1 if bool(piece & 8) else 1
        return (ty - fy) == fwd and tx == fx
    elif ptype == 3:
        for m in range(63):
            cx = fx + SPIRAL_DX[m]
            cy = fy + SPIRAL_DY[m]
            if not in_bounds(cx, cy): continue
            if cx == tx and cy == ty: return True
            if board[cy][cx] != 0: return False
        return False
    elif ptype == 4:
        return (abs(fx - tx), abs(fy - ty)) in [(1, 3), (3, 1)]
    elif ptype == 5:
        mask = QWORD_30A0[fy * 8 + fx]
        return bool((mask >> (ty * 8 + tx)) & 1)
    return False

def is_attacked(board, kx, ky, by_black):
    for y in range(8):
        for x in range(8):
            piece = board[y][x]
            if piece and bool(piece & 8) == by_black and (x != kx or y != ky):
                if attacks_1941(board, x, y, kx, ky):
                    return True
    return False

def kings_adjacent(board):
    wk = find_king(board, False)
    bk = find_king(board, True)
    if not wk or not bk: return False
    return abs(wk[0] - bk[0]) <= 1 and abs(wk[1] - bk[1]) <= 1

def is_valid_move(board, fx, fy, tx, ty):
    # check if there is a piece in the starting cell (fx, fy)
    piece = board[fy][fx]
    if not piece or (piece & 8) or board[ty][tx] == 9: 
        return False
    # check if the move is among the valid moves
    if (tx, ty) not in get_moves(board, fx, fy):
        return False
    
    nb = apply_move(board, fx, fy, tx, ty)
    return not kings_adjacent(nb) # the two kings cannot be adjacent

def is_checkmate(board):
    bk = find_king(board, True)
    if not bk: return False
    kx, ky = bk
    
    # check if king is under attack
    if not is_attacked(board, kx, ky, by_black=False):
        return False
        
    # check if there are escape routes
    for dy in range(-1, 2):
        for dx in range(-1, 2):
            if dx == 0 and dy == 0: continue
            tx, ty = kx + dx, ky + dy
            if in_bounds(tx, ty):
                t = board[ty][tx]
                if not t or not bool(t & 8):
                    nb = apply_move(board, kx, ky, tx, ty)
                    if not is_attacked(nb, tx, ty, by_black=False):
                        return False
    return True

# solver: try every valid move and check if checkmate
def solve(board):
    for fy in range(8):
        for fx in range(8):
            if board[fy][fx] and not (board[fy][fx] & 8):
                for tx, ty in get_moves(board, fx, fy):
                    if is_valid_move(board, fx, fy, tx, ty):
                        nb = apply_move(board, fx, fy, tx, ty)
                        if is_checkmate(nb):
                            return (fx, fy, tx, ty)
    return None

# parser: board string -> board object
def parse_board(text):
    board = [[0] * 8 for _ in range(8)]
    for line in text.split('\n'):
        parts = line.split()
        if len(parts) >= 9:
            try:
                row = int(parts[0])
                if 0 <= row <= 7:
                    for col in range(8):
                        board[row][col] = CHAR_TO_BYTE.get(parts[1 + col], 0)
            except ValueError: pass
    return board

def print_board(board):
    print("   " + " ".join(str(i) for i in range(8)))
    for row in range(7, -1, -1):
        cells = " ".join(BYTE_TO_CHAR.get(board[row][col], '?') for col in range(8))
        print(f"{row:2d} {cells}")

# execution
def run(proc_stdin, proc_stdout):
    for puzzle_num in range(1, 51):
        buf = ""
        while ">" not in buf:
            char = proc_stdout.read(1)
            if not char: break
            buf += char
            sys.stdout.write(char)
            sys.stdout.flush()

        board = parse_board(buf)
        result = solve(board)
        
        if result is None:
            print(f"[!] Puzzle {puzzle_num}: nessuna soluzione trovata!", file=sys.stderr)
            print_board(board)
            return

        fx, fy, tx, ty = result
        move = f"{fx},{fy} -> {tx},{ty}\n"

        piece = board[fy][fx]
        pc = BYTE_TO_CHAR.get(piece, '?')
        print(f"[{puzzle_num:2d}/50] {pc} ({fx},{fy})→({tx},{ty})", file=sys.stderr)

        proc_stdin.write(move.encode())
        proc_stdin.flush()

    time.sleep(0.5)
    out = proc_stdout.read()
    print(out, end="")

def main():
    proc = subprocess.Popen(
        ['./42'],
        stdin=subprocess.PIPE,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        bufsize=0
    )

    stdout_wrapper = io.TextIOWrapper(proc.stdout, encoding='utf-8', errors='replace')

    try: run(proc.stdin, stdout_wrapper)
    except BrokenPipeError: pass
    proc.wait()

if __name__ == '__main__':
    main()