import time
import math


class Square:
    tBlank = 0  # blank square '.'
    tWhite = 1  # blank W square which is also W's goal square
    tBlack = 2  # blank B square which is also B's goal square

    pBlank = 0  # blank no pawn
    pWhite = 1  # White pawn
    pBlack = 2  # Black pawn

    def __init__(self, square=0, pawn=0, row=0, col=0):
        self.square = square
        self.pawn = pawn
        self.row = row
        self.col = col
        self.location = (row, col)


class Halma():
    # map -> {"pawn starting location" : {"final end point reachable from start" : [list o =f intermediate square locations] }
    moveMap = {}

    def __init__(self, boardSize=16):
        # Create initial board setup to define goals squares
        board = [[None] * boardSize for _ in range(boardSize)]
        for row in range(boardSize):
            for col in range(boardSize):
                if row + col < 5:
                    element = Square(2, 2, row, col)
                elif 0 < row < 5 and row + col == 5:
                    element = Square(2, 2, row, col)
                elif row + col > 2 * (boardSize - 3) - 1:
                    element = Square(1, 1, row, col)
                elif boardSize - 1 > row > 10 and row + col == 2 * (boardSize - 3) - 1:
                    element = Square(1, 1, row, col)
                else:
                    element = Square(0, 0, row, col)

                board[row][col] = element

        # Save variables
        self.boardSize = boardSize
        self.board = board
        self.alphaBetaEnabled = True
        self.bGoals = [t for row in board for t in row if t.square == Square.pBlack]
        self.wGoals = [t for row in board for t in row if t.square == Square.pWhite]

    def updateBoard(self, board):
        self.board = board

    def minimax(self, depth, maxPlayer, maxTime, originalPlayer, a=float("-inf"), b=float("inf"), maxNode=True,
                prunes=0, boards=0):

        # Base case when either we hit the last node or we have a winner or if time limit exceeds
        if depth == 0 or self.determineWinner() or time.time() > maxTime:
            return self.evaluationFunction(maxPlayer), None, prunes, boards

        # Initial val, alpha and beta variables are setup -> valid moves are calculated
        bestMove = None
        if maxNode:
            bestVal = float("-inf")
            moves = self.getNextMoves(maxPlayer, originalPlayer)
        else:
            bestVal = float("inf")
            moves = self.getNextMoves((Square.pBlack if maxPlayer == Square.pWhite else Square.pWhite), originalPlayer)

        # For each move
        for move in moves:
            for to in move["to"]:

                # Stop if time limit exceeds
                if time.time() > maxTime:
                    return bestVal, bestMove, prunes, boards

                # Move pawn and make the previous pawn location as blank
                pawn = move["from"].pawn
                move["from"].pawn = Square.pBlank
                to.pawn = pawn
                boards += 1

                # Recursively call self
                val, _, newPrunes, newBoards = self.minimax(depth - 1, maxPlayer, maxTime, originalPlayer, a, b,
                                                            not maxNode, prunes, boards)
                prunes = newPrunes
                boards = newBoards

                # Move the pawn back to original position -> Refactor the board
                to.pawn = Square.pBlank
                move["from"].pawn = pawn

                if maxNode and val > bestVal:
                    bestVal = val
                    bestMove = (move["from"].location, to.location)
                    a = max(a, val)

                if not maxNode and val < bestVal:
                    bestVal = val
                    bestMove = (move["from"].location, to.location)
                    b = min(b, val)

                if self.alphaBetaEnabled and b <= a:
                    return bestVal, bestMove, prunes + 1, boards

        return bestVal, bestMove, prunes, boards

    def getNextMoves(self, player=1, originalPlayer=1):
        moves = []
        if player == originalPlayer:
            priorityTwoMove = []
        priorityOneMove = []
        checkGoals = [x.location for x in self.bGoals]
        if player == 1:
            checkGoals = [x.location for x in self.wGoals]
        for col in range(self.boardSize):
            for row in range(self.boardSize):
                currentSquare = self.board[row][col]

                # Skip squares that doesn't contain the player's pawns
                if currentSquare.pawn != player:
                    continue

                # List of moves from "from" to all possible final positions reachable from this

                move = {
                    "from": currentSquare,
                    "to": self.getMovesAtSquare(currentSquare, player, currentSquare)
                }
                if player == originalPlayer:
                    if currentSquare.location in checkGoals and len(move["to"]):
                        priorityOneMove.append(move)
                    else:
                        priorityTwoMove.append(move)
                else:
                    priorityOneMove.append(move)
                moves.append(move)
        if player == originalPlayer:
            moves = priorityOneMove if len(priorityOneMove) > 0 else priorityTwoMove
        else:
            moves = priorityOneMove
        return moves

    def getMovesAtSquare(self, square, player, oldSquare, moves=None, adjacent=True):

        if moves is None:
            moves = []

        row = square.location[0]
        col = square.location[1]

        checkGoals = [x.location for x in self.bGoals]
        if player == 1:
            checkGoals = [x.location for x in self.wGoals]

        # List of valid square types to move to
        validSquares = [Square.tBlank, Square.tWhite, Square.tBlack]

        # Removing moves that take the player back to his own goal
        if square.square != player:
            # print("Removed Player")
            validSquares.remove(player)

        # Removing moves that take the player out of the his enemy's initial position
        if square.square != Square.tBlank and square.square != player:
            validSquares.remove(Square.tBlank)

        # Find and save immediately adjacent moves
        if oldSquare.location not in self.moveMap:
            self.moveMap[oldSquare.location] = {}
        for colDelta in range(-1, 2):
            for rowDelta in range(-1, 2):

                # Check adjacent Squares
                newRow = row + rowDelta
                newCol = col + colDelta

                # Skip checking degenerate values
                if (newRow == row and newCol == col) or newRow < 0 or newCol < 0 or newRow >= self.boardSize or newCol >= self.boardSize:
                    continue

                # Handle moves that don't take to valid end points
                newSquare = self.board[newRow][newCol]
                if newSquare.square not in validSquares:
                    continue
                if newSquare.pawn == Square.pBlank:
                    if adjacent:  # Don't consider adjacent on subsequent calls
                        if square.location not in self.moveMap[oldSquare.location]:
                            self.moveMap[oldSquare.location][square.location] = set()
                        # if square.location not in self.moveMap[oldSquare.location]:
                            self.moveMap[oldSquare.location][square.location].add(newSquare.location)
                            if player == 2 and newSquare.location in checkGoals and (
                                    newSquare.location[0] < square.location[0] or newSquare.location[1] <
                                    square.location[1]):
                                continue
                            if player == 1 and newSquare.location in checkGoals and (
                                    newSquare.location[0] > square.location[0] or newSquare.location[1] >
                                    square.location[1]):
                                continue
                            moves.append(newSquare)
                    continue

                # Check jump squares
                newRow = newRow + rowDelta
                newCol = newCol + colDelta

                # Skip checking degenerate values
                if newRow < 0 or newCol < 0 or newRow >= self.boardSize or newCol >= self.boardSize:
                    continue

                # Handle moves that don't take to valid end points
                newSquare = self.board[newRow][newCol]
                if newSquare in moves or (newSquare.square not in validSquares):
                    continue
                if newSquare.pawn == Square.pBlank and newSquare not in moves:
                    # Prioritize jumps over single adjacent moves

                    if player == 2 and newSquare.location in checkGoals and (
                            newSquare.location[0] < square.location[0] or newSquare.location[1] <
                            square.location[1]):
                        continue
                    if player == 1 and newSquare.location in checkGoals and (
                            newSquare.location[0] > square.location[0] or newSquare.location[1] >
                            square.location[1]):
                        continue

                    moves.insert(0, newSquare)
                    if square.location not in self.moveMap[oldSquare.location]:
                        self.moveMap[oldSquare.location][square.location] = set()
                    self.moveMap[oldSquare.location][square.location].add(newSquare.location)
                    self.getMovesAtSquare(newSquare, player, oldSquare, moves, False)

        return moves

    def determineWinner(self):

        if all(g.pawn == Square.pWhite for g in self.bGoals):
            return Square.pWhite
        elif all(g.pawn == Square.pBlack for g in self.wGoals):
            return Square.pBlack
        else:
            return None

    def evaluationFunction(self, player):

        def euclideanDistance(p0, p1):
            return math.sqrt((p1[0] - p0[0]) ** 2 + (p1[1] - p0[1]) ** 2)

        def octileDistance(p0, p1):
            dx = abs(p0[0] - p1[0])
            dy = abs(p0[1] - p1[1])
            # Chebyshev constants
            D = 1
            D2 = round(2 ** 0.5, 1)
            return D * (dx + dy) + (D2 - 2 * D) * min(dx, dy)

        def chebyshevDistance(p0, p1):
            dx = abs(p0[0] - p1[0])
            dy = abs(p0[1] - p1[1])
            # Chebyshev constants
            D = 1
            D2 = 1
            return D * (dx + dy) + (D2 - 2 * D) * min(dx, dy)

        def manhattanDistance(p0, p1):
            dx = abs(p0[0] - p1[0])
            dy = abs(p0[1] - p1[1])
            return dx + dy

        value = 0
        distanceHeuristic = chebyshevDistance
        for col in range(self.boardSize):
            for row in range(self.boardSize):

                square = self.board[row][col]

                if square.pawn == Square.pWhite:
                    distances = [distanceHeuristic(square.location, g.location) for g in self.bGoals if
                                 g.pawn != Square.pWhite]
                    value -= max(distances) if len(distances) else -50

                elif square.pawn == Square.pBlack:
                    distances = [distanceHeuristic(square.location, g.location) for g in self.wGoals if
                                 g.pawn != Square.pBlack]
                    value += max(distances) if len(distances) else -50

        if player == Square.pBlack:
            value *= -1

        return value

    def getMovePath(self, moves, start, stop):
        stack = [(start, [start])]
        visited = set()
        while stack:
            (vertex, path) = stack.pop()
            if vertex not in visited:
                if vertex == stop:
                    return path
                visited.add(vertex)
                for neighbor in moves[vertex]:
                    if neighbor in moves:
                        stack.append((neighbor, path + [neighbor]))
                    elif neighbor == stop:
                        stack.append((neighbor, path + [neighbor]))


if __name__ == "__main__":
    start = time.time()
    fileInput = list()
    with open("input4.txt", "r") as f:
        for record in f.readlines():
            fileInput.append(record.strip())
        f.close()
    move = fileInput[0]
    playerColor = fileInput[1]
    timeRemaining = float(fileInput[2])
    boardConfig = list()
    for i in range(3, len(fileInput)):
        boardConfig.append([char for char in fileInput[i]])

    currentBoardConfig = list()
    for row in range(len(boardConfig)):
        currentBoardRow = list()
        for col in range(len(boardConfig[0])):
            if boardConfig[row][col] == 'B':
                pawn = Square(2, 2, row, col)
            elif boardConfig[row][col] == 'W':
                pawn = Square(1, 1, row, col)
            elif boardConfig[row][col] == '.':
                pawn = Square(0, 0, row, col)
            currentBoardRow.append(pawn)
        currentBoardConfig.append(currentBoardRow)

    if playerColor.lower() == "white":
        playerTurn = Square.pWhite
    else:
        playerTurn = Square.pBlack

    h = Halma(16)
    h.updateBoard(currentBoardConfig)
    checkGoals = [x.location for x in h.bGoals]
    if playerTurn == Square.pWhite:
        checkGoals = [x.location for x in h.wGoals]
    playerBase = False
    for col in range(h.boardSize):
        for row in range(h.boardSize):
            currentSquare = h.board[row][col]
            if currentSquare.pawn == playerTurn and (currentSquare.location in checkGoals):
                playerBase = True
                break
        if playerBase:
            break
    if playerBase:
        treeDepthSearch = 2  # Need to compute this
    else:
        treeDepthSearch = 3
    maxAvailableTime = time.time() + timeRemaining
    print("Tree depth:", treeDepthSearch)
    _, move, prunes, boards = h.minimax(treeDepthSearch, playerTurn, maxAvailableTime, playerTurn)
    print("Total number of boards/nodes generated : ", boards)
    print("Moves:", move)
    print("Total number of nodes pruned :", prunes)
    output = ""

    if (abs(move[0][0] - move[1][0]) == 1 or abs(move[0][1] - move[1][1])) == 1:
        output = "E " + str(move[0][1]) + "," + str(move[0][0]) + " " + str(move[1][1]) + "," + str(move[1][0])
    else:
        output = ""
        print(h.moveMap[move[0]])
        pathList = h.getMovePath(h.moveMap[move[0]], move[0], move[1])
        print("PathList:", pathList)
        i = 0
        j = 1
        while j != len(pathList):
            output += "J " + str(pathList[i][1]) + "," + str(pathList[i][0]) + " " + str(pathList[j][1]) + "," + str(
                pathList[j][0]) + "\n"
            i += 1
            j += 1
    with open("output.txt", "w+") as fWrite:
        fWrite.write(output.strip())
    end = time.time()

    # Print search result stats
    # print("Time to compute : ", round(end - start, 4))
