package com.github.ackintosh.graphql.repository

import com.github.ackintosh.graphql.type.Item
import com.github.ackintosh.graphql.type.Recommend
import org.springframework.stereotype.Component

@Component
class ItemRepository {
    // 取り急ぎデータはメモリに持っておくだけ
    private val recommendToItems = mapOf(
            1 to listOf(Item(1, "トートバッグ"), Item(2, "クッションケース")),
            2 to listOf(Item(3, "折りたたみテーブル"), Item(4, "ホワイトボード"))
    )

    fun find(recommend: Recommend) = recommendToItems[recommend.id]
}