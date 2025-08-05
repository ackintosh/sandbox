import org.junit.jupiter.api.Test
import java.time.DayOfWeek
import java.time.LocalDate
import java.time.temporal.WeekFields

class WeekTest {
    @Test
    fun test1() {
//        val date = LocalDate.of(2025, 7, 31) // 任意の日付
//        printWeekNumber(date)

        printWeekNumber(LocalDate.of(2025, 12, 26))
        printWeekNumber(LocalDate.of(2025, 12, 27))
        printWeekNumber(LocalDate.of(2025, 12, 28))
        printWeekNumber(LocalDate.of(2025, 12, 29))
        printWeekNumber(LocalDate.of(2025, 12, 30))
        printWeekNumber(LocalDate.of(2025, 12, 31))
        printWeekNumber(LocalDate.of(2026, 1, 1))
        printWeekNumber(LocalDate.of(2026, 1, 2))
        printWeekNumber(LocalDate.of(2026, 1, 3))
        printWeekNumber(LocalDate.of(2026, 1, 4))
        printWeekNumber(LocalDate.of(2026, 1, 5))
    }

    fun printWeekNumber(date: LocalDate) {
        val weekFields = WeekFields.of(DayOfWeek.MONDAY, 1)  // 週の開始：月曜日、最小週番号：1

        val weekOfYear = date.get(weekFields.weekOfYear())
        val prevDate = date.minusWeeks(1)
        val prevWeekOfYear = prevDate.get(weekFields.weekOfYear())

        // 直近の過去の土曜日を計算
        val nearestPastSaturday = date.with(java.time.temporal.TemporalAdjusters.previousOrSame(DayOfWeek.SATURDAY))
        val nearestPastSaturdayWeekOfYear = nearestPastSaturday.get(weekFields.weekOfYear())

        println("==================================")
        println("日付: $date (${date.dayOfWeek.getDisplayName(java.time.format.TextStyle.FULL, java.util.Locale.JAPANESE)})")
        println("年の第 $weekOfYear 週")
        println()
        println("前の週の日付: $prevDate (${prevDate.dayOfWeek.getDisplayName(java.time.format.TextStyle.FULL, java.util.Locale.JAPANESE)})")
        println("年の第 $prevWeekOfYear 週")
        println()
        println("直近の土曜日: $nearestPastSaturday (${nearestPastSaturday.dayOfWeek.getDisplayName(java.time.format.TextStyle.FULL, java.util.Locale.JAPANESE)})")
        println("年の第 $nearestPastSaturdayWeekOfYear 週")
        println()
    }
}
