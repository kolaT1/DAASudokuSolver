import org.sat4j.core.VecInt;
import org.sat4j.pb.SolverFactory;
import org.sat4j.specs.ISolver;
import org.sat4j.specs.TimeoutException;
import java.io.BufferedReader;
import java.io.FileReader;
import java.io.IOException;
public class SudokuSolver {

    private static ISolver solver = SolverFactory.newDefault();
    private static int SIZE;
    private static int VALUES;
    private static int[][][] X;

    private static int map(int i, int j, int k) {
        return (i * SIZE * VALUES) + (j * VALUES) + k + 1;
    }


    private static void addClause(int[] clause) {
        try {
            solver.addClause(new VecInt(clause));
        } catch (Exception e) {
            e.printStackTrace();
        }
    }

    private static void atLeastOnceInRow(int row, int value) {
        int[] clause = new int[SIZE];
        for (int j = 0; j < SIZE; j++) {
            clause[j] = X[row][j][value - 1];
        }
        addClause(clause);
    }

    private static void atMostOnceInRow(int row, int value) {
        for (int j1 = 0; j1 < SIZE - 1; j1++) {
            for (int j2 = j1 + 1; j2 < SIZE; j2++) {
                int[] clause = new int[]{-X[row][j1][value - 1], -X[row][j2][value - 1]};
                addClause(clause);
            }
        }
    }


    private static void atLeastOnceInCol(int col, int value) {
        int[] clause = new int[SIZE];
        for (int i = 0; i < SIZE; i++) {
            clause[i] = X[i][col][value - 1];
        }
        addClause(clause);
    }


    private static void atMostOnceInCol(int col, int value) {
        for (int i1 = 0; i1 < SIZE - 1; i1++) {
            for (int i2 = i1 + 1; i2 < SIZE; i2++) {
                int[] clause = new int[]{-X[i1][col][value - 1], -X[i2][col][value - 1]};
                addClause(clause);
            }
        }
    }

    //AtLeastOnceInBox
    private static void atLeastOnceInBox(int box, int value) {
        int[] clause = new int[SIZE];
        int index = 0;
        int startRow = (box / 3) * 3;
        int startCol = (box % 3) * 3;

        // Add variables corresponding to each cell in the box with the given value
        for (int row = startRow; row < startRow + 3; row++) {
            for (int col = startCol; col < startCol + 3; col++) {
                clause[index++] = X[row][col][value - 1];
            }
        }


        addClause(clause);
    }
     //AtMostOnceInABox
    private static void atMostOnceInBox(int box, int value) {

        for (int i = 0; i < SIZE; i++) {
            for (int j = i + 1; j < SIZE; j++) {
                int row1 = (box / 3) * 3 + (i / 3);
                int col1 = (box % 3) * 3 + (i % 3);
                int row2 = (box / 3) * 3 + (j / 3);
                int col2 = (box % 3) * 3 + (j % 3);


                int[] clause = new int[]{-X[row1][col1][value - 1], -X[row2][col2][value - 1]};
                addClause(clause);
            }
        }
    }
    // Constraint: A cell has at least one value
    private static void atLeastOneValue(int i, int j) {
        int[] clause = new int[VALUES];
        for (int k = 0; k < VALUES; k++) {
            clause[k] = X[i][j][k];
        }
        addClause(clause);
    }


    // Constraint: A cell has at most one value
    private static void atMostOneValue(int i, int j) {
        for (int k1 = 0; k1 < VALUES - 1; k1++) {
            for (int k2 = k1 + 1; k2 < VALUES; k2++) {
                int[] clause = new int[]{-X[i][j][k1], -X[i][j][k2]};
                addClause(clause);
            }
        }
    }
     //solver
    private static int[] solve() throws TimeoutException {
        int[] solution = null;
        if (solver.isSatisfiable()) {
            solution = new int[SIZE * SIZE];
            for (int i = 0; i < SIZE; i++) {
                for (int j = 0; j < SIZE; j++) {
                    for (int k = 0; k < VALUES; k++) {
                        if (solver.model(map(i, j, k))) {
                            solution[i * SIZE + j] = k + 1; // Added 1 to avoid using 0 as a value
                            break;
                        }
                    }
                }
            }
        }
        return solution;
    }

    private static boolean solve(int[][] puzzle) {
        SIZE = puzzle.length;
        VALUES = puzzle[0].length;
        X = new int[SIZE][SIZE][VALUES];

        for (int i = 0; i < SIZE; i++) {
            for (int j = 0; j < SIZE; j++) {
                for (int k = 0; k < VALUES; k++) {
                    X[i][j][k] = map(i, j, k);
                }
            }
        }

        solver.newVar(map(SIZE - 1, SIZE - 1, VALUES - 1));

        // Add constraints
        for (int i = 0; i < SIZE; i++) {
            for (int j = 0; j < SIZE; j++) {
                int value = puzzle[i][j];
                if (value != 0) {
                    atLeastOnceInRow(i, value);
                    atLeastOnceInCol(j, value);
                    atLeastOnceInBox((i / 3) * 3 + (j / 3), value);
                } else {
                    for (int k = 1; k <= VALUES; k++) {
                        atLeastOnceInRow(i, k);
                        atLeastOnceInCol(j, k);
                        atLeastOnceInBox((i / 3) * 3 + (j / 3), k);
                    }
                }
                atMostOnceInRow(i, value);
                atMostOnceInCol(j, value);
                atMostOnceInBox((i / 3) * 3 + (j / 3), value);
            }
        }

        // SAT problem
        try {
            return solver.isSatisfiable();
        } catch (TimeoutException e) {
            return false;
        }
    }

    public static void main(String[] args) throws TimeoutException {
        try {
            BufferedReader reader = new BufferedReader(new FileReader(""));
            String line;
            while ((line = reader.readLine()) != null) {
                String[] parts = line.split(" ");
                SIZE = Integer.parseInt(parts[0]);
                VALUES = Integer.parseInt(parts[1]);

                X = new int[SIZE][SIZE][VALUES];


                for (int i = 0; i < SIZE; i++) {
                    for (int j = 0; j < SIZE; j++) {
                        for (int k = 0; k < VALUES; k++) {
                            X[i][j][k] = map(i, j, k);
                        }
                    }
                }

                int row = 0;
                int col = 0;
                while ((line = reader.readLine()) != null) {
                    String[] parts2 = line.split(" ");
                    for (int i = 0; i < parts2.length; i++) {
                        int value = Integer.parseInt(parts2[i]);
                        if (value > 0) {
                            addClause(new int[]{X[row][col][value - 1]});
                        }
                        col++;
                        if (col == SIZE) {
                            col = 0;
                            row++;
                        }
                    }
                    if (row == SIZE) {
                        break;
                    }
                }

                // Add constraints for each cell
                for (int i = 0; i < SIZE; i++) {
                    for (int j = 0; j < SIZE; j++) {
                        atLeastOneValue(i, j);
                        for (int k = 0; k < VALUES; k++) {
                            atMostOneValue(i, j);
                        }
                    }
                }

                // Add constraints for each row
                for (int value = 1; value <= VALUES; value++) {
                    for (int row1 = 0; row1 < SIZE; row1++) {
                        atLeastOnceInRow(row1, value);
                        atMostOnceInRow(row1, value);
                    }
                }

                // Add constraints for each column
                for (int value = 1; value <= VALUES; value++) {
                    for (int col1 = 0; col1 < SIZE; col1++) {
                        atLeastOnceInCol(col1, value);
                        atMostOnceInCol(col1, value);
                    }
                }

                // Add constraints for each box
                for (int value = 1; value <= VALUES; value++) {
                    for (int box = 0; box < SIZE; box++) {
                        atLeastOnceInBox(box, value);
                        atMostOnceInBox(box, value);
                    }
                }

                System.out.println(solve());
            }
            reader.close();
        } catch (IOException e) {
            e.printStackTrace();
        } catch (TimeoutException e) {
            throw new RuntimeException(e);
        }
        if (solver.isSatisfiable()) {
            System.out.println("satisfying");
        } else {
            System.out.println("not solvable");
        }
    }
}
