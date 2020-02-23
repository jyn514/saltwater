// fail
typedef long L;
    int main() {
            long long ll;  // should declare ll as a long long
            L L ll2; // should be an error, declares `L` as a long and then there needs to be a comma between L and ll2
    }
