package com.github.ackintosh.graphql.repository

import com.github.ackintosh.graphql.type.Recommend
import org.springframework.stereotype.Component

@Component
class RecommendRepository {
    // 取り急ぎデータはメモリに持っておくだけ
    private val recommends = mapOf(
            1 to Recommend(1, "テレワークにお役立ちのアイテム集合！", listOf(1, 2)),
            2 to Recommend(2, "わけあり商品！", listOf(3, 4))
    )

    fun all(): List<Recommend> {
        println("RecommendRepository::all()")
        return recommends.values.toList()
    }

    fun find(id: Int) : Recommend? {
        println("RecommendRepository::find()")
        return recommends[id]
    }
}