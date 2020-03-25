package com.github.ackintosh.graphql.repository

import com.github.ackintosh.graphql.type.Item
import org.springframework.stereotype.Component

@Component
class ItemRepository {
    // 取り急ぎデータはメモリに持っておくだけ
    private val itemList = mapOf(
            1 to Item(1, "トートバッグ"),
            2 to Item(2, "クッションケース"),
            3 to Item(3, "折りたたみテーブル"),
            4 to Item(4, "ホワイトボード")
    )

    fun find(ids: List<Int>): List<Item> {
        println("ItemRepository::find()")
        return itemList.filterKeys { ids.contains(it) }.values.toList()
    }
}